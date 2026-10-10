import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.FermionicDensity
import OAI.Analysis.CoulombIonization.Variational.FullCoulomb

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom
section CoulombCoercivity

lemma weakGraph_norm_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [IsLocallyFiniteMeasure (volume : Measure E)]
    {ι : Type*} [Fintype ι] (v : ι → E) (F : weakGraph v) :
    ‖F‖ ^ 2 = ‖F.val none‖ ^ 2 + ∑ i : ι, ‖F.val (some i)‖ ^ 2 := by
  change ‖F.val‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_option]

@[simp] lemma fermionGraphValue_apply {N : ℕ} (F : fermionGraph N) (s : Spins N) :
    (fermionGraphValue N F).val s = (F.val s).val none := rfl

lemma fermionGraph_norm_sq {N : ℕ} (F : fermionGraph N) :
    ‖F‖ ^ 2 = ‖fermionGraphValue N F‖ ^ 2 +
      ∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3, ‖graphComponent s (some (i, a)) F‖ ^ 2 := by
  have hF : ‖F‖ ^ 2 = ∑ s : Spins N, ‖F.val s‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ _
  have hv : ‖fermionGraphValue N F‖ ^ 2 = ∑ s : Spins N, ‖(F.val s).val none‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 _ _
  rw [hF, hv]
  simp only [weakGraph_norm_sq, Fintype.sum_prod_type, Finset.sum_add_distrib,
    graphComponent_apply]

lemma graphNuclear_bound {N : ℕ} {Z : ℝ} (hZ : 0 ≤ Z) (F : fermionGraph N)
    (s : Spins N) (i : Fin N) :
    Z * ‖graphNuclear s i F‖ ^ 2 ≤
      (1 / 4 : ℝ) * (∑ a : Fin 3, ‖graphComponent s (some (i, a)) F‖ ^ 2) +
        Z ^ 2 * ‖graphComponent s none F‖ ^ 2 := by
  have hh := linear_coulomb_bound (ContinuousLinearMap.proj i) (fun a => direction i a)
    (by intro a; simp [direction]) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hZ)
    (Lp.memLp ((F.val s).val none)) (fun a => Lp.memLp ((F.val s).val (some (i, a))))
    (fun a => (mem_weakGraph (sectorDirections N) (F.val s).val).mp (F.val s).property (i, a))
  simp only [ContinuousLinearMap.proj_apply, ← lp_norm_sq] at hh
  have hn := graphNuclear_norm_sq s i F
  change ‖graphNuclear s i F‖ ^ 2 = ∫ x, ‖(F.val s).val none x‖ ^ 2 / ‖x i‖ at hn
  rw [← hn] at hh
  change 2 * (2 * Z) * ‖graphNuclear s i F‖ ^ 2 ≤
    (∑ a : Fin 3, ‖graphComponent s (some (i, a)) F‖ ^ 2) +
      (2 * Z) ^ 2 * ‖graphComponent s none F‖ ^ 2 at hh
  nlinarith

lemma graphValue_norm_sq {N : ℕ} (F : fermionGraph N) :
    ‖fermionGraphValue N F‖ ^ 2 = ∑ s : Spins N, ‖graphComponent s none F‖ ^ 2 := by
  change ‖(fermionGraphValue N F).val‖ ^ 2 = _
  exact PiLp.norm_sq_eq_of_L2 _ _

attribute [local irreducible] graphComponent graphNuclear graphPair fermionGraphValue

lemma nuclear_sum_arithmetic {S : Type*} [Fintype S] {N : ℕ} (Z : ℝ)
    (A : S → Fin N → ℝ) (K : S → Fin N → Fin 3 → ℝ) (M : S → ℝ)
    (h : ∀ s i, Z * A s i ≤ (1 / 4 : ℝ) * (∑ a, K s i a) + Z ^ 2 * M s) :
    Z * (∑ s, ∑ i, A s i) ≤ (1 / 4 : ℝ) * (∑ s, ∑ i, ∑ a, K s i a) +
      (N : ℝ) * Z ^ 2 * ∑ s, M s := by
  have hs := Finset.sum_le_sum (s := Finset.univ) fun s _ =>
    Finset.sum_le_sum (s := Finset.univ) fun i _ => h s i
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, mul_comm (Z ^ 2) (N : ℝ)] using hs

lemma graphNuclear_sum_bound {N : ℕ} {Z : ℝ} (hZ : 0 ≤ Z) (F : fermionGraph N) :
    Z * (∑ s : Spins N, ∑ i : Fin N, ‖graphNuclear s i F‖ ^ 2) ≤
      (1 / 4 : ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        ‖graphComponent s (some (i, a)) F‖ ^ 2) +
      (N : ℝ) * Z ^ 2 * ‖fermionGraphValue N F‖ ^ 2 := by
  have hs := nuclear_sum_arithmetic Z (fun s i => ‖graphNuclear s i F‖ ^ 2)
    (fun s i a => ‖graphComponent s (some (i, a)) F‖ ^ 2)
    (fun s => ‖graphComponent s none F‖ ^ 2) (graphNuclear_bound hZ F)
  exact hs.trans_eq (congrArg (fun M : ℝ =>
    (1 / 4 : ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
      ‖graphComponent s (some (i, a)) F‖ ^ 2) + (N : ℝ) * Z ^ 2 * M)
      (graphValue_norm_sq F).symm)

lemma coulombFormOperator_inner_lower {N : ℕ} (Z : ℝ) (F : fermionGraph N) :
    (1 / 2 : ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
      ‖graphComponent s (some (i, a)) F‖ ^ 2) -
      Z * (∑ s : Spins N, ∑ i : Fin N, ‖graphNuclear s i F‖ ^ 2) ≤
        (⟪F, coulombFormOperator Z N F⟫_ℂ).re := by
  have hk : (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
      ∫ x, ‖(graphFormVector F).gradient s i a x‖ ^ 2) =
      ∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3, ‖graphComponent s (some (i, a)) F‖ ^ 2 := by
    simp only [lp_norm_sq, graphComponent_apply, graphFormVector]
  have hn : (∑ s : Spins N, ∑ i : Fin N, ∫ x, ‖(graphFormVector F).value s x‖ ^ 2 / ‖x i‖) =
      ∑ s : Spins N, ∑ i : Fin N, ‖graphNuclear s i F‖ ^ 2 := by
    simp only [graphNuclear_norm_sq]
  conv_rhs => rw [coulombFormOperator_inner]; unfold formEnergy; rw [hk, hn]
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro s _
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact integral_nonneg fun x => div_nonneg (sq_nonneg _) (norm_nonneg _)
  · exact le_rfl

lemma coercivity_arithmetic {K M A E C : ℝ} (hM : 0 ≤ M)
    (hA : A ≤ 1 / 4 * K + C * M) (hE : 1 / 2 * K - A ≤ E) :
    1 / 4 * (M + K) ≤ E + (C + 1) * M := by nlinarith

lemma coulombFormOperator_coercive_bound {N : ℕ} {Z : ℝ} (hZ : 0 ≤ Z) (F : fermionGraph N) :
    (1 / 4 : ℝ) * ‖F‖ ^ 2 ≤ (⟪F, coulombFormOperator Z N F⟫_ℂ).re +
      ((N : ℝ) * Z ^ 2 + 1) * ‖fermionGraphValue N F‖ ^ 2 := by
  conv_lhs => rw [fermionGraph_norm_sq F]
  exact coercivity_arithmetic (sq_nonneg _) (graphNuclear_sum_bound hZ F)
    (coulombFormOperator_inner_lower Z F)

def shiftedCoulombFormOperator (Z : ℝ) (N : ℕ) : fermionGraph N →L[ℂ] fermionGraph N :=
  coulombFormOperator Z N + (((N : ℝ) * Z ^ 2 + 1 : ℝ) : ℂ) •
    (fermionGraphValue N).adjoint.comp (fermionGraphValue N)

lemma shiftedCoulombFormOperator_selfAdjoint (Z : ℝ) (N : ℕ) :
    IsSelfAdjoint (shiftedCoulombFormOperator Z N) := by
  change (shiftedCoulombFormOperator Z N).adjoint = shiftedCoulombFormOperator Z N
  simp only [shiftedCoulombFormOperator, map_add, map_smulₛₗ,
    (coulombFormOperator_selfAdjoint Z N).adjoint_eq,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  simp

lemma shiftedCoulombFormOperator_inner (Z : ℝ) (N : ℕ) (F : fermionGraph N) :
    (⟪F, shiftedCoulombFormOperator Z N F⟫_ℂ).re =
      (⟪F, coulombFormOperator Z N F⟫_ℂ).re +
        ((N : ℝ) * Z ^ 2 + 1) * ‖fermionGraphValue N F‖ ^ 2 := by
  simp only [shiftedCoulombFormOperator, add_apply, smul_apply, inner_add_right,
    inner_smul_right, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, gram_inner]

theorem shiftedCoulombFormOperator_coercive {Z : ℝ} (hZ : 0 ≤ Z) (N : ℕ) (F : fermionGraph N) :
    (1 / 4 : ℝ) * ‖F‖ ^ 2 ≤ (⟪F, shiftedCoulombFormOperator Z N F⟫_ℂ).re := by
  rw [shiftedCoulombFormOperator_inner]
  exact coulombFormOperator_coercive_bound hZ F

end CoulombCoercivity

lemma fermionPermutation_ae {N : ℕ} (π : Equiv.Perm (Fin N)) (F : SectorHilbert N)
    (s : Spins N) :
    (fun x => fermionPermutation π F s x) =ᵐ[volume]
      fun x => (((Equiv.Perm.sign π : ℤ) : ℂ)) * F (s ∘ π) (x ∘ π) := by
  rw [fermionPermutation_apply]
  filter_upwards [Lp.coeFn_smul (((Equiv.Perm.sign π : ℤ) : ℂ))
    (Lp.compMeasurePreserving (permuteConfiguration π) (permuteConfiguration_preserving π)
      (F (s ∘ π))),
    Lp.coeFn_compMeasurePreserving (F (s ∘ π)) (permuteConfiguration_preserving π)] with x hx hy
  simpa only [Pi.smul_apply, smul_eq_mul, Function.comp_apply, permuteConfiguration_apply] using hx.trans (congrArg
    (fun z : ℂ => (((Equiv.Perm.sign π : ℤ) : ℂ)) * z) hy)

lemma mem_fermionSpace_ae {N : ℕ} (F : SectorHilbert N) :
    F ∈ fermionSpace N ↔ ∀ (π : Equiv.Perm (Fin N)) s, ∀ᵐ x,
      F (s ∘ π) (x ∘ π) = (((Equiv.Perm.sign π : ℤ) : ℂ)) * F s x := by
  rw [mem_fermionSpace]
  constructor
  · intro h π s
    have hp := fermionPermutation_ae π F s
    rw [h π] at hp
    filter_upwards [hp] with x hx
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hs | hs
    · simpa [hs] using hx.symm
    · simpa [hs] using congrArg Neg.neg hx.symm
  · intro h π
    apply PiLp.ext
    intro s
    apply Lp.ext
    filter_upwards [fermionPermutation_ae π F s, h π s] with x hx hy
    rw [hx, hy]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hs | hs <;> simp [hs]

lemma graphFormVector_admissible {N : ℕ} (F : fermionGraph N)
    (hn : ‖fermionGraphValue N F‖ ^ 2 = 1) : FormAdmissible (graphFormVector F) := by
  refine ⟨fun s => Lp.memLp _, fun s i a => Lp.memLp _, ?_, ?_, ?_, ?_, ?_⟩
  · intro s i a φ hφ hcφ
    exact ((mem_weakGraph (sectorDirections N) (F.val s).val).mp (F.val s).property
      (i, a)) φ hφ hcφ
  · intro π s
    exact (mem_fermionSpace_ae _).mp (fermionGraphValue N F).property π s
  · have hmass := graphValue_norm_sq F
    rw [hn] at hmass
    simpa only [lp_norm_sq, graphComponent_apply, graphFormVector] using hmass.symm
  · intro s i
    exact nuclear_integrable i (Lp.memLp _) (fun a => Lp.memLp _)
      (fun a => (mem_weakGraph (sectorDirections N) (F.val s).val).mp (F.val s).property (i, a))
  · intro s i j hij
    exact pair_integrable i j hij (Lp.memLp _) (fun a => Lp.memLp _)
      (fun a => (mem_weakGraph (sectorDirections N) (F.val s).val).mp (F.val s).property (i, a))

def admissibleWeakGraph {N : ℕ} (ψ : FormVector N) (hψ : FormAdmissible ψ) (s : Spins N) :
    weakGraph (sectorDirections N) := by
  let F : WeakGraphAmbient (Configuration N) (Fin N × Fin 3) := WithLp.toLp 2 fun k =>
    match k with
    | none => (hψ.1 s).toLp (ψ.value s)
    | some ia => (hψ.2.1 s ia.1 ia.2).toLp (ψ.gradient s ia.1 ia.2)
  refine ⟨F, (mem_weakGraph (sectorDirections N) F).mpr ?_⟩
  intro ia
  exact IsWeakDerivative.congr_ae (hψ.2.2.1 s ia.1 ia.2)
    (hψ.1 s).coeFn_toLp.symm (hψ.2.1 s ia.1 ia.2).coeFn_toLp.symm

@[simp] lemma admissibleWeakGraph_value {N : ℕ} (ψ : FormVector N) (hψ : FormAdmissible ψ)
    (s : Spins N) : (admissibleWeakGraph ψ hψ s).val none = (hψ.1 s).toLp (ψ.value s) := rfl

@[simp] lemma admissibleWeakGraph_gradient {N : ℕ} (ψ : FormVector N) (hψ : FormAdmissible ψ)
    (s : Spins N) (i : Fin N) (a : Fin 3) :
    (admissibleWeakGraph ψ hψ s).val (some (i, a)) =
      (hψ.2.1 s i a).toLp (ψ.gradient s i a) := rfl

def admissibleGraph {N : ℕ} (ψ : FormVector N) (hψ : FormAdmissible ψ) : fermionGraph N := by
  let F : SectorGraph N := WithLp.toLp 2 (admissibleWeakGraph ψ hψ)
  refine ⟨F, (mem_fermionSpace_ae (sectorGraphValue N F)).mpr ?_⟩
  intro π s
  have hp := (permuteConfiguration_preserving π).quasiMeasurePreserving.ae
    ((hψ.1 (s ∘ π)).coeFn_toLp)
  simp only [permuteConfiguration_apply] at hp
  filter_upwards [hp, (hψ.1 s).coeFn_toLp, hψ.2.2.2.1 π s] with x hx hy hz
  change (hψ.1 (s ∘ π)).toLp _ (x ∘ π) = _
  change (hψ.1 (s ∘ π)).toLp _ (x ∘ π) = _ at hx
  change _ = (((Equiv.Perm.sign π : ℤ) : ℂ)) * (hψ.1 s).toLp _ x
  rw [hx, hy, hz]

lemma graphFormVector_admissibleGraph_value {N : ℕ} (ψ : FormVector N)
    (hψ : FormAdmissible ψ) (s : Spins N) :
    (graphFormVector (admissibleGraph ψ hψ)).value s =ᵐ[volume] ψ.value s := by
  simpa only [graphFormVector, admissibleGraph, WithLp.ofLp_toLp,
    admissibleWeakGraph_value] using (hψ.1 s).coeFn_toLp

lemma graphFormVector_admissibleGraph_gradient {N : ℕ} (ψ : FormVector N)
    (hψ : FormAdmissible ψ) (s : Spins N) (i : Fin N) (a : Fin 3) :
    (graphFormVector (admissibleGraph ψ hψ)).gradient s i a =ᵐ[volume] ψ.gradient s i a := by
  simpa only [graphFormVector, admissibleGraph, WithLp.ofLp_toLp,
    admissibleWeakGraph_gradient] using (hψ.2.1 s i a).coeFn_toLp

lemma admissibleGraph_norm {N : ℕ} (ψ : FormVector N) (hψ : FormAdmissible ψ) :
    ‖fermionGraphValue N (admissibleGraph ψ hψ)‖ ^ 2 = 1 := by
  calc
    _ = ∑ s : Spins N, ∫ x, ‖(graphFormVector (admissibleGraph ψ hψ)).value s x‖ ^ 2 := by
      rw [graphValue_norm_sq]
      simp only [lp_norm_sq, graphComponent_apply, graphFormVector]
    _ = ∑ s : Spins N, ∫ x, ‖ψ.value s x‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro s _
      apply integral_congr_ae
      filter_upwards [graphFormVector_admissibleGraph_value ψ hψ s] with x hx
      rw [hx]
    _ = 1 := hψ.2.2.2.2.1

lemma formEnergy_congr_ae {N : ℕ} (Z : ℝ) (ψ φ : FormVector N)
    (hv : ∀ s, ψ.value s =ᵐ[volume] φ.value s)
    (hg : ∀ s i a, ψ.gradient s i a =ᵐ[volume] φ.gradient s i a) :
    formEnergy Z ψ = formEnergy Z φ := by
  have hk : (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3, ∫ x, ‖ψ.gradient s i a x‖ ^ 2) =
      ∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3, ∫ x, ‖φ.gradient s i a x‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro a _
    apply integral_congr_ae
    filter_upwards [hg s i a] with x hx
    rw [hx]
  have hn : (∑ s : Spins N, ∑ i : Fin N, ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i‖) =
      ∑ s : Spins N, ∑ i : Fin N, ∫ x, ‖φ.value s x‖ ^ 2 / ‖x i‖ := by
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [hv s] with x hx
    rw [hx]
  have hp : (∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N,
      if i < j then ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i - x j‖ else 0) =
      ∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N,
      if i < j then ∫ x, ‖φ.value s x‖ ^ 2 / ‖x i - x j‖ else 0 := by
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · apply integral_congr_ae
      filter_upwards [hv s] with x hx
      rw [hx]
    · rfl
  unfold formEnergy
  rw [hk, hn, hp]

theorem full_form_value_set (Z : ℝ) (N : ℕ) :
    {e : ℝ | ∃ ψ : FormVector N, FormAdmissible ψ ∧ formEnergy Z ψ = e} =
      {e : ℝ | ∃ F : fermionGraph N, ‖fermionGraphValue N F‖ ^ 2 = 1 ∧
        (⟪F, coulombFormOperator Z N F⟫_ℂ).re = e} := by
  ext e
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    refine ⟨admissibleGraph ψ hψ, admissibleGraph_norm ψ hψ, ?_⟩
    rw [coulombFormOperator_inner]
    exact formEnergy_congr_ae Z _ ψ (graphFormVector_admissibleGraph_value ψ hψ)
      (graphFormVector_admissibleGraph_gradient ψ hψ)
  · rintro ⟨F, hF, rfl⟩
    exact ⟨graphFormVector F, graphFormVector_admissible F hF,
      (coulombFormOperator_inner Z N F).symm⟩

end CoulombAtom

end

end OAI
