import OAI.Analysis.KadisonKastler.BoundaryPolarMeasurable
import OAI.Analysis.KadisonKastler.NonsingularBoundary
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

namespace OAI

/-! # Removing the boundary variables by double ergodicity

The diagonal comparison gives the vector field `L* a Ω`.  Its covariance
is derived from the product intertwiner and the tracial right action.
Double ergodicity is used only for this actual bounded measurable field.
-/

namespace KadisonKastler

universe uG uD uH

open MeasureTheory Filter

noncomputable section

section Measurability

variable {P H : Type*} [MeasurableSpace P] [NormedAddCommGroup H]
  [NormedSpace ℂ H] {μ : Measure P}

/-- Strongly measurable evaluations of an operator field can be applied
to a varying strongly measurable vector. No operator-norm measurability
of the field is required. -/
theorem aestronglyMeasurable_field_apply (T : P → H →L[ℂ] H)
    (hT : ∀ ξ, AEStronglyMeasurable (fun p => T p ξ) μ)
    (v : P → H) (hv : AEStronglyMeasurable v μ) :
    AEStronglyMeasurable (fun p => T p (v p)) μ := by
  have haux (w : P → H) (hw : StronglyMeasurable w) :
      AEStronglyMeasurable (fun p => T p (w p)) μ := by
    induction w, hw using StronglyMeasurable.induction with
    | @ind ξ s hs =>
      convert (hT ξ).indicator hs using 1
      funext p
      by_cases hp : p ∈ s <;> simp [hp]
    | add hf hg hfg hdisj ihf ihg =>
      convert ihf.add ihg using 1
      funext p
      simp only [Pi.add_apply, map_add]
    | lim hf hg ih hlim =>
      exact aestronglyMeasurable_of_tendsto_ae atTop ih
        (Eventually.of_forall fun p => (T p).continuous.tendsto _ |>.comp (hlim p))
  exact (haux (hv.mk v) hv.stronglyMeasurable_mk).congr
    (hv.ae_eq_mk.symm.mono fun p hp => congrArg (T p) hp)

end Measurability

section Operators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The operator identity behind the equivariance of `L* a Ω`. -/
theorem boundary_intertwiner_adjoint (L K U V : unitary (H →L[ℂ] H))
    (h : (L : H →L[ℂ] H) * U = (V : H →L[ℂ] H) * K) :
    star (L : H →L[ℂ] H) * V = (U : H →L[ℂ] H) * star (K : H →L[ℂ] H) := by
  calc
    _ = (star (L : H →L[ℂ] H) * ((V : H →L[ℂ] H) * K)) *
        star (K : H →L[ℂ] H) := by
      simp only [mul_assoc, Unitary.mul_star_self_of_mem K.property, mul_one]
    _ = (star (L : H →L[ℂ] H) * ((L : H →L[ℂ] H) * U)) *
        star (K : H →L[ℂ] H) := by rw [h]
    _ = _ := by
      simp only [← mul_assoc, Unitary.star_mul_self_of_mem L.property, one_mul]

/-- Diagonal covariance follows from the genuine right-action identities. -/
theorem boundary_comparison_vector_covariance
    (L K U W Z R a b : unitary (H →L[ℂ] H)) (Ω : H)
    (hL : (L : H →L[ℂ] H) * U = ((W : H →L[ℂ] H) * R) * K)
    (ha : (a : H →L[ℂ] H) = ((W : H →L[ℂ] H) * b) * star (Z : H →L[ℂ] H))
    (hR : (R : H →L[ℂ] H) * b = (b : H →L[ℂ] H) * R)
    (hΩ : (R : H →L[ℂ] H) Ω = star (Z : H →L[ℂ] H) Ω) :
    star (L : H →L[ℂ] H) ((a : H →L[ℂ] H) Ω) =
      (U : H →L[ℂ] H) (star (K : H →L[ℂ] H) ((b : H →L[ℂ] H) Ω)) := by
  have hi := boundary_intertwiner_adjoint L K U (W * R) hL
  have hr := congrArg (fun t : H →L[ℂ] H => t Ω) hR
  change (R : H →L[ℂ] H) ((b : H →L[ℂ] H) Ω) =
    (b : H →L[ℂ] H) ((R : H →L[ℂ] H) Ω) at hr
  rw [hΩ] at hr
  rw [ha]
  change star (L : H →L[ℂ] H)
    ((W : H →L[ℂ] H) ((b : H →L[ℂ] H) (star (Z : H →L[ℂ] H) Ω))) = _
  rw [← hr]
  exact congrArg (fun t : H →L[ℂ] H => t ((b : H →L[ℂ] H) Ω)) hi

/-- The scalar phase supplied by the invariant vector defines a unitary
scalar operator. -/
def scalarUnitaryOfNormOne (z : ℂ) (hz : ‖z‖ = 1) : unitary (H →L[ℂ] H) :=
  ⟨z • 1, by
    have hzz : star z * z = 1 := by
      rw [Complex.star_def, Complex.conj_mul', hz]
      norm_num
    have hzz' : z * star z = 1 := by rw [mul_comm, hzz]
    constructor <;> simp only [star_smul, star_one, smul_mul_assoc, mul_smul_comm,
      one_mul, smul_smul, hzz, hzz', one_smul]⟩

/-- A constant unit vector of the form `L* a Ω = z Ω` gives the normalized
unitary `z a* L` fixing `Ω`. -/
theorem normalized_boundary_unitary_fixes
    (L a : unitary (H →L[ℂ] H)) (Ω : H) (z : ℂ) (hz : ‖z‖ = 1)
    (hv : star (L : H →L[ℂ] H) ((a : H →L[ℂ] H) Ω) = z • Ω) :
    ((scalarUnitaryOfNormOne z hz * star a * L : unitary (H →L[ℂ] H)) :
      H →L[ℂ] H) Ω = Ω := by
  have h := congrArg (fun ξ => star (a : H →L[ℂ] H) ((L : H →L[ℂ] H) ξ)) hv
  have hLL (ξ : H) : (L : H →L[ℂ] H) (star (L : H →L[ℂ] H) ξ) = ξ :=
    congrArg (fun t : H →L[ℂ] H => t ξ) (Unitary.mul_star_self_of_mem L.property)
  have haa (ξ : H) : star (a : H →L[ℂ] H) ((a : H →L[ℂ] H) ξ) = ξ :=
    congrArg (fun t : H →L[ℂ] H => t ξ) (Unitary.star_mul_self_of_mem a.property)
  change z • (star (a : H →L[ℂ] H) ((L : H →L[ℂ] H) Ω)) = Ω
  simpa only [map_smul, hLL, haa] using h.symm

theorem normalized_boundary_unitary_distance
    (L a : unitary (H →L[ℂ] H)) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖((scalarUnitaryOfNormOne z hz * star a * L : unitary (H →L[ℂ] H)) :
      H →L[ℂ] H) - 1‖ ≤
      ‖z - 1‖ + ‖(a : H →L[ℂ] H) - 1‖ + ‖(L : H →L[ℂ] H) - 1‖ := by
  have hs : ‖((scalarUnitaryOfNormOne (H := H) z hz : unitary (H →L[ℂ] H)) :
      H →L[ℂ] H) - 1‖ ≤ ‖z - 1‖ := by
    change ‖z • (1 : H →L[ℂ] H) - 1‖ ≤ _
    have heq : z • (1 : H →L[ℂ] H) - 1 = (z - 1) • (1 : H →L[ℂ] H) := by
      rw [sub_smul, one_smul]
    rw [heq, norm_smul]
    have h₁ : ‖(1 : H →L[ℂ] H)‖ ≤ 1 :=
      norm_unitary_le_one (1 : unitary (H →L[ℂ] H))
    calc
      _ ≤ ‖z - 1‖ * 1 := mul_le_mul_of_nonneg_left h₁ (norm_nonneg _)
      _ = _ := mul_one _
  have ha : ‖((star a : unitary (H →L[ℂ] H)) : H →L[ℂ] H) - 1‖ =
      ‖(a : H →L[ℂ] H) - 1‖ := by
    simpa only [Unitary.coe_star, star_sub, star_one] using
      norm_star ((a : H →L[ℂ] H) - 1)
  exact (norm_unitary_mul_sub_one_le (scalarUnitaryOfNormOne z hz * star a) L).trans
    (add_le_add ((norm_unitary_mul_sub_one_le (scalarUnitaryOfNormOne z hz)
      (star a)).trans (add_le_add hs ha.le)) le_rfl)

/-- The one-sided product intertwiner gives the precise unitary image of
each group vector after scalar normalization. -/
theorem normalized_boundary_unitary_image
    (L K a b U W : unitary (H →L[ℂ] H)) (Ω : H) (z : ℂ)
    (hL : (L : H →L[ℂ] H) * U = (W : H →L[ℂ] H) * K)
    (hK : star (K : H →L[ℂ] H) ((b : H →L[ℂ] H) Ω) = z • Ω) :
    (z • (star (a : H →L[ℂ] H) * L)) ((U : H →L[ℂ] H) Ω) =
      (star (a : H →L[ℂ] H) * W * b) Ω := by
  have hb := congrArg (fun ξ => (K : H →L[ℂ] H) ξ) hK
  have hKK (ξ : H) : (K : H →L[ℂ] H) (star (K : H →L[ℂ] H) ξ) = ξ :=
    congrArg (fun t : H →L[ℂ] H => t ξ) (Unitary.mul_star_self_of_mem K.property)
  have hb' : (b : H →L[ℂ] H) Ω = z • (K : H →L[ℂ] H) Ω := by
    simpa only [map_smul, hKK] using hb
  change z • (star (a : H →L[ℂ] H) ((L : H →L[ℂ] H) ((U : H →L[ℂ] H) Ω))) = _
  have hLΩ : (L : H →L[ℂ] H) ((U : H →L[ℂ] H) Ω) =
      (W : H →L[ℂ] H) ((K : H →L[ℂ] H) Ω) :=
    congrArg (fun t : H →L[ℂ] H => t Ω) hL
  rw [hLΩ]
  simpa only [mul_apply_eq_comp, map_smul] using
    congrArg (fun ξ => star (a : H →L[ℂ] H) ((W : H →L[ℂ] H) ξ)) hb'.symm

/-- The image unitaries stay close to the original group elements. -/
theorem boundary_unitary_image_distance (a b W U : unitary (H →L[ℂ] H)) :
    ‖star (a : H →L[ℂ] H) * W * b - U‖ ≤
      ‖(a : H →L[ℂ] H) - 1‖ + ‖(W : H →L[ℂ] H) - U‖ +
        ‖(b : H →L[ℂ] H) - 1‖ := by
  calc
    _ ≤ ‖star (a : H →L[ℂ] H) * W * b - (W : H →L[ℂ] H) * b‖ +
        ‖(W : H →L[ℂ] H) * b - U‖ := by
          simpa only [dist_eq_norm] using dist_triangle
            (star (a : H →L[ℂ] H) * W * b) ((W : H →L[ℂ] H) * b) (U : H →L[ℂ] H)
    _ ≤ ‖star (a : H →L[ℂ] H) * W * b - (W : H →L[ℂ] H) * b‖ +
        (‖(W : H →L[ℂ] H) * b - (U : H →L[ℂ] H) * b‖ +
          ‖(U : H →L[ℂ] H) * b - U‖) := by
      have ht : ‖(W : H →L[ℂ] H) * b - U‖ ≤
          ‖(W : H →L[ℂ] H) * b - (U : H →L[ℂ] H) * b‖ +
            ‖(U : H →L[ℂ] H) * b - U‖ := by
        simpa only [dist_eq_norm] using dist_triangle
          ((W : H →L[ℂ] H) * b) ((U : H →L[ℂ] H) * b) (U : H →L[ℂ] H)
      exact add_le_add le_rfl ht
    _ = _ := by
      have h₁ : star (a : H →L[ℂ] H) * W * b - (W : H →L[ℂ] H) * b =
          (star (a : H →L[ℂ] H) - 1) * W * b := by noncomm_ring
      have h₂ : (W : H →L[ℂ] H) * b - (U : H →L[ℂ] H) * b =
          ((W : H →L[ℂ] H) - U) * b := by noncomm_ring
      have h₃ : (U : H →L[ℂ] H) * b - U =
          (U : H →L[ℂ] H) * ((b : H →L[ℂ] H) - 1) := by noncomm_ring
      rw [h₁, h₂, h₃]
      simp only [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
      have ha : star (a : H →L[ℂ] H) - 1 = star ((a : H →L[ℂ] H) - 1) := by simp
      rw [ha, norm_star]
      ring

end Operators

section Ergodic

variable {G : Type uG} {D : Type uD} {H : Type uH} [Group G] [MeasurableSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {μ : Measure D} [SFinite μ] [NeZero (μ.prod μ)]

/-- Applying genuine double ergodicity to the diagonal comparison field
produces its scalar phase and the quantitative near-one bound. -/
theorem exists_boundary_scalar_of_doubleErgodic
    (α : NonsingularAction G D μ) (herg : UnitaryDoubleErgodic.{uG, uD, uH} α)
    (σ : G →* unitary (H →L[ℂ] H)) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (hfixed : ∀ v : H, (∀ g, (σ g : H →L[ℂ] H) v = v) → ∃ z : ℂ, v = z • Ω)
    (L a : D × D → unitary (H →L[ℂ] H))
    (hLm : ∀ ξ, AEStronglyMeasurable
      (fun p => star (L p : H →L[ℂ] H) ξ) (μ.prod μ))
    (ham : AEStronglyMeasurable (fun p => (a p : H →L[ℂ] H) Ω) (μ.prod μ))
    (hcov : ∀ g, ∀ᵐ p ∂μ.prod μ,
      star (L (α.diagonal.toPerm g p) : H →L[ℂ] H)
        ((a (α.diagonal.toPerm g p) : H →L[ℂ] H) Ω) =
      (σ g : H →L[ℂ] H) (star (L p : H →L[ℂ] H) ((a p : H →L[ℂ] H) Ω)))
    {ε : ℝ} (hnear : ∀ᵐ p ∂μ.prod μ,
      ‖star (L p : H →L[ℂ] H) * (a p : H →L[ℂ] H) - 1‖ ≤ ε) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ‖z - 1‖ ≤ ε ∧
      (∀ᵐ p ∂μ.prod μ,
        star (L p : H →L[ℂ] H) ((a p : H →L[ℂ] H) Ω) = z • Ω) := by
  let f : D × D → H := fun p =>
    star (L p : H →L[ℂ] H) ((a p : H →L[ℂ] H) Ω)
  have hfm : AEStronglyMeasurable f (μ.prod μ) :=
    aestronglyMeasurable_field_apply _ hLm _ ham
  have hfn (p : D × D) : ‖f p‖ = 1 := by
    dsimp [f]
    rw [← Unitary.coe_star, Unitary.norm_map, Unitary.norm_map, hΩ]
  obtain ⟨v, hv, hfv⟩ := herg H σ f hfm
    ⟨1, Eventually.of_forall fun p => (hfn p).le⟩ hcov
  obtain ⟨z, rfl⟩ := hfixed v hv
  have hz : ‖z‖ = 1 := by
    obtain ⟨p, hp⟩ := hfv.exists
    have hh := hfn p
    rw [hp, norm_smul, hΩ, mul_one] at hh
    exact hh
  refine ⟨z, hz, ?_, hfv⟩
  have hh : ∀ᵐ p ∂μ.prod μ, ‖z - 1‖ ≤ ε := by
    filter_upwards [hfv, hnear] with p hp hn
    have hb := ContinuousLinearMap.le_opNorm
      (star (L p : H →L[ℂ] H) * (a p : H →L[ℂ] H) - 1) Ω
    change ‖f p - Ω‖ ≤ _ at hb
    have heq : z • Ω - Ω = (z - 1) • Ω := by rw [sub_smul, one_smul]
    rw [hp, heq, norm_smul, hΩ, mul_one, mul_one] at hb
    exact hb.trans hn
  exact hh.exists.choose_spec

/-- The field used in double ergodicity is equivariant as a consequence
of the product intertwiner, diagonal comparison and tracial right action. -/
theorem exists_boundary_scalar_from_comparison
    (α : NonsingularAction G D μ) (herg : UnitaryDoubleErgodic.{uG, uD, uH} α)
    (σ : G →* unitary (H →L[ℂ] H)) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (hfixed : ∀ v : H, (∀ g, (σ g : H →L[ℂ] H) v = v) → ∃ z : ℂ, v = z • Ω)
    (L a : D × D → unitary (H →L[ℂ] H))
    (W R : G → D → unitary (H →L[ℂ] H))
    (hLm : ∀ ξ, AEStronglyMeasurable
      (fun p => star (L p : H →L[ℂ] H) ξ) (μ.prod μ))
    (ham : AEStronglyMeasurable (fun p => (a p : H →L[ℂ] H) Ω) (μ.prod μ))
    (hL : ∀ g, ∀ᵐ p ∂μ.prod μ,
      (L p : H →L[ℂ] H) * σ g =
        ((W g p.1 : H →L[ℂ] H) * R g p.2) * L (α.diagonal.toPerm g⁻¹ p))
    (ha : ∀ g, ∀ᵐ p ∂μ.prod μ,
      (a p : H →L[ℂ] H) =
        ((W g p.1 : H →L[ℂ] H) * a (α.diagonal.toPerm g⁻¹ p)) *
          star (W g p.2 : H →L[ℂ] H))
    (hR : ∀ g, ∀ᵐ p ∂μ.prod μ,
      (R g p.2 : H →L[ℂ] H) * a (α.diagonal.toPerm g⁻¹ p) =
        (a (α.diagonal.toPerm g⁻¹ p) : H →L[ℂ] H) * R g p.2)
    (hRΩ : ∀ g, ∀ᵐ p ∂μ.prod μ,
      (R g p.2 : H →L[ℂ] H) Ω = star (W g p.2 : H →L[ℂ] H) Ω)
    {ε : ℝ} (hnear : ∀ᵐ p ∂μ.prod μ,
      ‖star (L p : H →L[ℂ] H) * (a p : H →L[ℂ] H) - 1‖ ≤ ε) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ‖z - 1‖ ≤ ε ∧
      (∀ᵐ p ∂μ.prod μ,
        star (L p : H →L[ℂ] H) ((a p : H →L[ℂ] H) Ω) = z • Ω) := by
  apply exists_boundary_scalar_of_doubleErgodic α herg σ Ω hΩ hfixed L a hLm ham ?_ hnear
  intro g
  have hback : ∀ᵐ p ∂μ.prod μ,
      star (L p : H →L[ℂ] H) ((a p : H →L[ℂ] H) Ω) =
        (σ g : H →L[ℂ] H) (star (L (α.diagonal.toPerm g⁻¹ p) : H →L[ℂ] H)
          ((a (α.diagonal.toPerm g⁻¹ p) : H →L[ℂ] H) Ω)) := by
    filter_upwards [hL g, ha g, hR g, hRΩ g] with p hp hpa hpr hpΩ
    exact boundary_comparison_vector_covariance (L p) (L (α.diagonal.toPerm g⁻¹ p))
      (σ g) (W g p.1) (W g p.2) (R g p.2) (a p) (a (α.diagonal.toPerm g⁻¹ p)) Ω
      hp hpa hpr hpΩ
  filter_upwards [(α.diagonal.quasi g).ae hback] with p hp
  have hs : α.diagonal.toPerm g⁻¹ (α.diagonal.toPerm g p) = p := by
    rw [← α.diagonal.mul_apply, inv_mul_cancel, α.diagonal.one_apply]
  simpa only [hs] using hp

omit [TopologicalSpace.SeparableSpace H] in
/-- Choose one pair on which the scalar-vector relation and all group
intertwiners hold simultaneously, including their separate translates. -/
theorem exists_simultaneous_boundary_normalization [Countable G]
    (α : NonsingularAction G D μ) (Ω : H)
    (L a : D × D → unitary (H →L[ℂ] H))
    (U : G → unitary (H →L[ℂ] H)) (W : G → D → unitary (H →L[ℂ] H))
    (z : ℂ) (hz : ‖z‖ = 1)
    (hvec : ∀ᵐ p ∂μ.prod μ,
      star (L p : H →L[ℂ] H) ((a p : H →L[ℂ] H) Ω) = z • Ω)
    (hL : ∀ g, ∀ᵐ p ∂μ.prod μ,
      (L p : H →L[ℂ] H) * U g = (W g p.1 : H →L[ℂ] H) *
        L (α.toPerm g⁻¹ p.1, p.2))
    {εL εa εW : ℝ} (hznear : ‖z - 1‖ ≤ εL + εa)
    (hLn : ∀ᵐ p ∂μ.prod μ, ‖(L p : H →L[ℂ] H) - 1‖ ≤ εL)
    (ha : ∀ᵐ p ∂μ.prod μ, ‖(a p : H →L[ℂ] H) - 1‖ ≤ εa)
    (hW : ∀ g, ∀ᵐ p ∂μ.prod μ,
      ‖(W g p.1 : H →L[ℂ] H) - U g‖ ≤ εW) :
    ∃ (p : D × D) (S : unitary (H →L[ℂ] H)),
      (S : H →L[ℂ] H) Ω = Ω ∧
      ‖(S : H →L[ℂ] H) - 1‖ ≤ 2 * (εL + εa) ∧
      ∀ g, (S : H →L[ℂ] H) ((U g : H →L[ℂ] H) Ω) =
        ((star (a p) * W g p.1 * a (α.toPerm g⁻¹ p.1, p.2) :
          unitary (H →L[ℂ] H)) : H →L[ℂ] H) Ω ∧
        ‖((star (a p) * W g p.1 * a (α.toPerm g⁻¹ p.1, p.2) :
          unitary (H →L[ℂ] H)) : H →L[ℂ] H) - U g‖ ≤ 2 * εa + εW := by
  let P : G → D × D → Prop := fun g p =>
    ((L p : H →L[ℂ] H) * U g = (W g p.1 : H →L[ℂ] H) *
      L (α.toPerm g⁻¹ p.1, p.2)) ∧
    (star (L p : H →L[ℂ] H) ((a p : H →L[ℂ] H) Ω) = z • Ω) ∧
    ‖(L p : H →L[ℂ] H) - 1‖ ≤ εL ∧
    ‖(a p : H →L[ℂ] H) - 1‖ ≤ εa ∧ ‖(W g p.1 : H →L[ℂ] H) - U g‖ ≤ εW
  have hP : ∀ g, ∀ᵐ p ∂μ.prod μ, P g p := by
    intro g
    filter_upwards [hL g, hvec, hLn, ha, hW g] with p hp hv hl ha hw
    exact ⟨hp, hv, hl, ha, hw⟩
  obtain ⟨p, hp⟩ := α.prod.exists_simultaneous_point P hP
  have hp0 (g : G) : P g p := by
    simpa only [NonsingularAction.prod_apply, α.one_apply] using hp (1, 1) g
  let S := scalarUnitaryOfNormOne z hz * star (a p) * L p
  refine ⟨p, S, normalized_boundary_unitary_fixes (L p) (a p) Ω z hz (hp0 1).2.1, ?_, ?_⟩
  · exact (normalized_boundary_unitary_distance (L p) (a p) z hz).trans
      (by linarith [(hp0 1).2.2.1, (hp0 1).2.2.2.1])
  intro g
  let q : D × D := (α.toPerm g⁻¹ p.1, p.2)
  have hq : P 1 q := by
    simpa only [NonsingularAction.prod_apply, α.one_apply] using hp (g⁻¹, 1) 1
  constructor
  · change (z • (star (a p : H →L[ℂ] H) * L p)) ((U g : H →L[ℂ] H) Ω) = _
    exact normalized_boundary_unitary_image (L p) (L q) (a p) (a q) (U g) (W g p.1)
      Ω z (hp0 g).1 hq.2.1
  · have hh := boundary_unitary_image_distance (a p) (a q) (W g p.1) (U g)
    exact hh.trans (by linarith [(hp0 g).2.2.2.1, (hp0 g).2.2.2.2, hq.2.2.2.1])

end Ergodic

end

end KadisonKastler

end OAI
