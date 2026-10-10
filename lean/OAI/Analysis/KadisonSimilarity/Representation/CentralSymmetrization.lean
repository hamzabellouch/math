import OAI.Analysis.KadisonSimilarity.Representation.FiniteSymmetrization
import OAI.Analysis.KadisonSimilarity.Representation.SpectralSteps
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.GroupTheory.NoncommPiCoprod

namespace OAI

/-! # Averaging over finite families of central projections

The finite sign groups and their averages are constructed explicitly. A weak
operator cluster point of the net indexed by finite projection families
commutes with every central projection. The final passage to the whole center
uses only the already stated spectral-step specialization of Blackadar.
-/

noncomputable section
namespace KadisonSimilarity

open Filter ContinuousLinearMapWOT
open scoped Topology Classical

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The center as a concrete von Neumann algebra. -/
def vonNeumannCenter (P : VonNeumannAlgebra H) : VonNeumannAlgebra H where
  toStarSubalgebra := P.toStarSubalgebra ⊓ P.commutant.toStarSubalgebra
  centralizer_centralizer' := by
    have he : (P : Set (H →L[ℂ] H)) ∩ (P.commutant : Set (H →L[ℂ] H)) =
        Set.centralizer ((P : Set (H →L[ℂ] H)) ∪ P.commutant) := by
      rw [Set.centralizer_union]
      rw [← VonNeumannAlgebra.coe_commutant, ← VonNeumannAlgebra.coe_commutant]
      simp only [VonNeumannAlgebra.commutant_commutant, Set.inter_comm]
    change Set.centralizer (Set.centralizer
      ((P : Set (H →L[ℂ] H)) ∩ P.commutant)) =
      ((P : Set (H →L[ℂ] H)) ∩ P.commutant)
    rw [he]
    exact Set.centralizer_centralizer_centralizer
      ((P : Set (H →L[ℂ] H)) ∪ P.commutant)

@[simp] theorem mem_vonNeumannCenter (P : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    a ∈ vonNeumannCenter P ↔ a ∈ P ∧ a ∈ P.commutant := Iff.rfl

/-- The projection index is unrestricted in cardinality. -/
def CentralProjection (P : VonNeumannAlgebra H) :=
  {p : H →L[ℂ] H // p ∈ vonNeumannCenter P ∧ IsStarProjection p}

private def centralUnitarySubgroup (P : VonNeumannAlgebra H) :
    Subgroup (unitary (H →L[ℂ] H)) where
  carrier := {u | (u : H →L[ℂ] H) ∈ vonNeumannCenter P}
  one_mem' := (vonNeumannCenter P).one_mem
  mul_mem' := fun ha hb => (vonNeumannCenter P).mul_mem ha hb
  inv_mem' := fun hu => by
    change (star _ : H →L[ℂ] H) ∈ vonNeumannCenter P
    exact star_mem hu

private theorem centralUnitary_commute (P : VonNeumannAlgebra H)
    (u v : centralUnitarySubgroup P) : Commute u v := by
  change u * v = v * u
  apply Subtype.ext
  apply Subtype.ext
  exact ((VonNeumannAlgebra.mem_commutant_iff.mp v.property.2)
    (u.val : H →L[ℂ] H) u.property.1)

private def centralReflection {P : VonNeumannAlgebra H} (p : CentralProjection P) :
    centralUnitarySubgroup P :=
  ⟨⟨2 * p.val - 1, p.property.2.two_mul_sub_one_mem_unitary⟩, by
    change 2 * p.val - 1 ∈ vonNeumannCenter P
    rw [two_mul]
    exact (vonNeumannCenter P).sub_mem
      ((vonNeumannCenter P).add_mem p.property.1 p.property.1)
      (vonNeumannCenter P).one_mem⟩

private theorem centralReflection_square {P : VonNeumannAlgebra H}
    (p : CentralProjection P) : centralReflection p * centralReflection p = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  change (2 * p.val - 1) * (2 * p.val - 1) = 1
  rw [two_mul]
  have hp := p.property.2.isIdempotentElem.eq
  simp only [mul_sub, sub_mul, mul_add, add_mul, hp, one_mul, mul_one]
  abel

private theorem intUnit_eq_one_or_neg_one (g : ℤˣ) : g = 1 ∨ g = -1 := by
  exact Int.units_eq_one_or g

private def centralSignHom {P : VonNeumannAlgebra H} (p : CentralProjection P) :
    ℤˣ →* centralUnitarySubgroup P where
  toFun g := if g = 1 then 1 else centralReflection p
  map_one' := by simp
  map_mul' g h := by
    rcases intUnit_eq_one_or_neg_one g with rfl | rfl <;>
      rcases intUnit_eq_one_or_neg_one h with rfl | rfl <;>
      simp [centralReflection_square]

private def centralSignRepresentation (P : VonNeumannAlgebra H)
    (s : Finset (CentralProjection P)) : (s → ℤˣ) →* (H →L[ℂ] H) :=
  (unitary (H →L[ℂ] H)).subtype.comp
    ((centralUnitarySubgroup P).subtype.comp
      (MonoidHom.noncommPiCoprod (fun p : s => centralSignHom p.val)
        (fun _ _ _ _ _ => centralUnitary_commute P _ _)))

private theorem centralSignRepresentation_mem (P : VonNeumannAlgebra H)
    (s : Finset (CentralProjection P)) (g : s → ℤˣ) :
    centralSignRepresentation P s g ∈ P := by
  exact (MonoidHom.noncommPiCoprod (fun p : s => centralSignHom p.val)
    (fun _ _ _ _ _ => centralUnitary_commute P _ _) g).property.1

private theorem norm_centralSignRepresentation_le (P : VonNeumannAlgebra H)
    (s : Finset (CentralProjection P)) (g : s → ℤˣ) :
    ‖centralSignRepresentation P s g‖ ≤ 1 := by
  let u : unitary (H →L[ℂ] H) :=
    (MonoidHom.noncommPiCoprod (fun p : s => centralSignHom p.val)
      (fun _ _ _ _ _ => centralUnitary_commute P _ _) g).val
  change ‖(u : H →L[ℂ] H)‖ ≤ 1
  have h := CStarRing.norm_coe_unitary_mul u (1 : H →L[ℂ] H)
  simpa only [mul_one] using h.le.trans (IsStarProjection.norm_le 1 (.one _))

private theorem centralSignRepresentation_single (P : VonNeumannAlgebra H)
    (s : Finset (CentralProjection P)) (p : s) :
    centralSignRepresentation P s (Pi.mulSingle p (-1)) = 2 * p.val.val - 1 := by
  classical
  simp only [centralSignRepresentation, MonoidHom.comp_apply]
  simp [centralSignHom, centralReflection]

/-- The finite average belonging to a finite family of central projections. -/
def centralProjectionTwirl (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H)
    (s : Finset (CentralProjection P)) : H →L[ℂ] H :=
  finiteTwirl (centralSignRepresentation P s) Y

theorem centralProjectionTwirl_commute (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H)
    (s : Finset (CentralProjection P)) (p : CentralProjection P) (hp : p ∈ s) :
    commutator (centralProjectionTwirl P Y s) p.val = 0 := by
  classical
  have h := finiteTwirl_commute (centralSignRepresentation P s) Y
    (Pi.mulSingle (⟨p, hp⟩ : s) (-1))
  rw [centralSignRepresentation_single] at h
  change commutator (centralProjectionTwirl P Y s) (2 * p.val - 1) = 0 at h
  have he : commutator (centralProjectionTwirl P Y s) (2 * p.val - 1) =
      (2 : ℂ) • commutator (centralProjectionTwirl P Y s) p.val := by
    simp only [two_mul, commutator, mul_sub, sub_mul, mul_add, add_mul, mul_one, one_mul]
    module
  rw [he] at h
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

/-- Weak-operator compactness applies to arbitrary directed nets. -/
theorem exists_weakOperator_net_cluster {J : Type*} (l : Filter J) [l.NeBot]
    (T : J → H →L[ℂ] H) {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ j, ‖T j‖ ≤ R) :
    ∃ S : H →L[ℂ] H, ‖S‖ ≤ R ∧ MapClusterPt (ofCLM S) l (fun j => ofCLM (T j)) := by
  have hev : ∀ᶠ j in l, ofCLM (T j) ∈
      {B : H →WOT[ℂ] H | ‖toCLM B‖ ≤ R} := Eventually.of_forall hbound
  obtain ⟨S, hS, hcluster⟩ :=
    (isCompact_weakOperator_ball (H := H) R hR).exists_mapClusterPt_of_frequently hev.frequently
  exact ⟨toCLM S, hS, hcluster⟩

theorem norm_sub_le_of_weakOperator_net_cluster {J : Type*} {l : Filter J}
    (T : J → H →L[ℂ] H) (S A : H →L[ℂ] H)
    (hcluster : MapClusterPt (ofCLM S) l (fun j => ofCLM (T j)))
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ᶠ j in l, ‖T j - A‖ ≤ c) : ‖S - A‖ ≤ c := by
  have hclosed : IsClosed {B : H →WOT[ℂ] H | ‖toCLM B - A‖ ≤ c} :=
    (isCompact_weakOperator_ball (H := H) c hc).isClosed.preimage
      (continuous_id.sub continuous_const)
  exact hclosed.mem_of_mapClusterPt hcluster hbound

theorem norm_commutator_le_of_weakOperator_net_cluster {J : Type*} {l : Filter J}
    (T : J → H →L[ℂ] H) (S A : H →L[ℂ] H)
    (hcluster : MapClusterPt (ofCLM S) l (fun j => ofCLM (T j)))
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ᶠ j in l, ‖commutator (T j) A‖ ≤ c) :
    ‖commutator S A‖ ≤ c := by
  have hclosed : IsClosed {B : H →WOT[ℂ] H | ‖commutator (toCLM B) A‖ ≤ c} :=
    (isCompact_weakOperator_ball (H := H) c hc).isClosed.preimage
      ((continuous_id.mul_const (ofCLM A)).sub (continuous_id.const_mul (ofCLM A)))
  exact hclosed.mem_of_mapClusterPt hcluster hbound

/-- No countability assumption is needed: finite sign averages have a
common weak cluster point commuting with every central projection. -/
theorem exists_central_projection_symmetrization (P : VonNeumannAlgebra H)
    (Y : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hscalar : scalarCommutatorNorm P Y ≤ δ) :
    ∃ Y₁ : H →L[ℂ] H, ‖Y₁‖ ≤ ‖Y‖ ∧ ‖Y₁ - Y‖ ≤ δ ∧
      (∀ p : CentralProjection P, commutator Y₁ p.val = 0) := by
  let T := centralProjectionTwirl P Y
  have hnorm s : ‖T s‖ ≤ ‖Y‖ :=
    norm_finiteTwirl_le _ (norm_centralSignRepresentation_le P s) Y
  obtain ⟨Y₁, hY₁, hcluster⟩ := exists_weakOperator_net_cluster
    (atTop : Filter (Finset (CentralProjection P))) T (norm_nonneg Y) hnorm
  refine ⟨Y₁, hY₁, ?_, ?_⟩
  · apply norm_sub_le_of_weakOperator_net_cluster T Y₁ Y hcluster hδ
    apply Eventually.of_forall
    intro s
    rw [norm_sub_rev]
    apply norm_sub_finiteTwirl_le _ (norm_centralSignRepresentation_le P s)
    intro g
    calc
      ‖commutator Y (centralSignRepresentation P s g)‖ ≤
          scalarCommutatorNorm P Y * ‖centralSignRepresentation P s g‖ :=
        norm_commutator_le_scalarCommutatorNorm P Y _ (centralSignRepresentation_mem P s g)
      _ ≤ δ * 1 := mul_le_mul hscalar (norm_centralSignRepresentation_le P s g)
        (norm_nonneg _) hδ
      _ = δ := mul_one _
  · intro p
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    apply norm_commutator_le_of_weakOperator_net_cluster T Y₁ p.val hcluster le_rfl
    filter_upwards [eventually_ge_atTop ({p} : Finset (CentralProjection P))] with s hs
    have hp : p ∈ s := hs (Finset.mem_singleton_self p)
    simp only [T, centralProjectionTwirl_commute P Y s p hp, norm_zero, le_refl]

/-- Norm approximation by spectral steps extends projection commutation to
commutation with the whole von Neumann algebra. -/
theorem commutator_zero_of_spectralSteps (C : VonNeumannAlgebra H)
    (approximation : SpectralStepApproximation C) (T : H →L[ℂ] H)
    (hprojection : ∀ p : H →L[ℂ] H, p ∈ C → IsStarProjection p → commutator T p = 0) :
    ∀ a : H →L[ℂ] H, a ∈ C → commutator T a = 0 := by
  have hself (a : H →L[ℂ] H) (ha : a ∈ C) (has : star a = a) :
      commutator T a = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    apply le_of_forall_pos_le_add
    intro ε hε
    let η := ε / (2 * ‖T‖ + 1)
    have hη : 0 < η := by dsimp [η]; positivity
    obtain ⟨n, r, c, e, he, _, herr⟩ := approximation a ha has η hη
    have hstep : commutator T (spectralStep r c e) = 0 := by
      rw [commutator_spectralStep]
      apply Finset.sum_eq_zero
      intro i _
      rw [hprojection (e i) (he i).1 ⟨(he i).2.2, (he i).2.1⟩, smul_zero]
    have heq : commutator T a = commutator T (a - spectralStep r c e) := by
      change innerDerivation T a = innerDerivation T (a - spectralStep r c e)
      rw [map_sub]
      change commutator T a = commutator T a - commutator T (spectralStep r c e)
      rw [hstep, sub_zero]
    have hηε : 2 * ‖T‖ * η ≤ ε := by
      have hden : 0 < 2 * ‖T‖ + 1 := by positivity
      dsimp [η]
      rw [← mul_div_assoc, div_le_iff₀ hden]
      nlinarith
    calc
      ‖commutator T a‖ = ‖commutator T (a - spectralStep r c e)‖ := congrArg norm heq
      _ ≤ 2 * ‖T‖ * ‖a - spectralStep r c e‖ := norm_commutator_le _ _
      _ ≤ 2 * ‖T‖ * η := mul_le_mul_of_nonneg_left herr (by positivity)
      _ ≤ 0 + ε := by simpa only [zero_add] using hηε
  intro a ha
  have hstar : star a ∈ C := star_mem ha
  let b : H →L[ℂ] H := realPart a
  let c : H →L[ℂ] H := imaginaryPart a
  have hb : b ∈ C := by
    dsimp [b]
    rw [realPart_apply_coe, ← Complex.coe_smul]
    exact C.toStarSubalgebra.smul_mem (C.add_mem ha hstar) _
  have hc : c ∈ C := by
    dsimp [c]
    rw [imaginaryPart_apply_coe, ← Complex.coe_smul]
    exact C.toStarSubalgebra.smul_mem
      (C.toStarSubalgebra.smul_mem (C.sub_mem ha hstar) _) _
  change innerDerivation T a = 0
  rw [← realPart_add_I_smul_imaginaryPart a, map_add, map_smul]
  change commutator T b + Complex.I • commutator T c = 0
  rw [hself b hb (realPart a).property, hself c hc (imaginaryPart a).property,
    smul_zero, add_zero]

/-- Central averaging for the global reduction. The only published input
is spectral approximation inside the actual center; the average, its norm
control, and its exact central commutation are all constructed above. -/
theorem exists_central_symmetrization (P : VonNeumannAlgebra H)
    (approximation : SpectralStepApproximation (vonNeumannCenter P))
    (Y : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hscalar : scalarCommutatorNorm P Y ≤ δ) :
    ∃ Y₁ : H →L[ℂ] H, ‖Y₁‖ ≤ ‖Y‖ ∧ ‖Y₁ - Y‖ ≤ δ ∧
      scalarCommutatorNorm P Y₁ ≤ 3 * δ ∧
      ∀ a : H →L[ℂ] H, a ∈ vonNeumannCenter P → commutator Y₁ a = 0 := by
  obtain ⟨Y₁, hnorm, hclose, hprojection⟩ :=
    exists_central_projection_symmetrization P Y hδ hscalar
  refine ⟨Y₁, hnorm, hclose, ?_, ?_⟩
  · apply (scalarCommutatorNorm_le_iff P Y₁ (by positivity)).mpr
    intro a ha
    calc
      ‖commutator Y₁ a‖ ≤ scalarCommutatorNorm P Y * ‖a‖ + 2 * δ * ‖a‖ :=
        norm_commutator_le_of_approx Y₁ Y a
          (norm_commutator_le_scalarCommutatorNorm P Y a ha) hclose
      _ ≤ δ * ‖a‖ + 2 * δ * ‖a‖ := by gcongr
      _ = (3 * δ) * ‖a‖ := by ring
  · apply commutator_zero_of_spectralSteps (vonNeumannCenter P) approximation Y₁
    intro p hp hps
    exact hprojection ⟨p, hp, hps⟩

end KadisonSimilarity

end

end OAI
