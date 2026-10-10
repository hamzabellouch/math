import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConeIdealStrictWidth
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GeneratorConjugation

namespace OAI

/-! # Strict-width inclusions for actual group conjugation -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra Filter
open scoped Topology

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

local instance : NormedAddCommGroup (cartanRootIdeal H) :=
  NormedAddCommGroup.induced _ _ (finBasis ℝ (cartanRootIdeal H)).equivFun.toLinearMap
    (finBasis ℝ (cartanRootIdeal H)).equivFun.injective
local instance : NormedSpace ℝ (cartanRootIdeal H) :=
  NormedSpace.induced ℝ _ _ (finBasis ℝ (cartanRootIdeal H)).equivFun.toLinearMap

variable {G A : Type*} [Group G] [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

variable
  (Exp : cartanRootIdeal H → G) (j : cartanRootIdeal H →ₗ⁅ℝ⁆ A)
  (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
  (hmatch : ∀ x, ρ (Exp x) = algebraExpUnit (j x))

include hρ hmatch in
/-- The flow in the width estimate is precisely conjugation by the
corresponding generator exponential in the actual group. -/
theorem coneIdealLetterFlow_exp_conjugation (i : Fin M.letterCount)
    (t : ℝ) (v : M.coneWordIdeal C) :
    Exp (M.coneIdealLetterFlow C i t v : cartanRootIdeal H) =
      Exp (t • M.letter i) * Exp (v : cartanRootIdeal H) * (Exp (t • M.letter i))⁻¹ := by
  let D := toEnd ℝ (cartanRootIdeal H) (cartanRootIdeal H) (M.letter i)
  have hD : D ^ M.bound = 0 := by
    apply LinearMap.ext
    intro x
    rw [Module.End.pow_apply, LinearMap.zero_apply]
    have hx := iterate_toEnd_mem_lowerCentralSeries ℝ (cartanRootIdeal H)
      (cartanRootIdeal H) (M.letter i) x M.bound
    rw [M.bound_zero] at hx
    exact hx
  have hm := finiteEndFlow_map (M.coneWordIdeal C).incl.toLinearMap
    (M.coneIdealLetterAdjoint C i) D (fun _ => rfl) M.bound t v
  change Exp ((M.coneWordIdeal C).incl (finiteEndFlow
    (M.coneIdealLetterAdjoint C i) M.bound t v)) = _
  calc
    _ = Exp (finiteEndFlow D M.bound t (v : cartanRootIdeal H)) := congrArg Exp hm
    _ = _ := by
      rw [finiteEndFlow_eq_exp D hD]
      exact exp_ad_eq_group_conjugation Exp j ρ hρ hmatch (M.letter i) v t

include hρ hmatch in
theorem coneIdeal_group_conjugation_absorbed
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C b₀ s β)
    (i : Fin M.letterCount) (hi : s i = 0)
    {a b lo α : ℝ} (ha : 0 ≤ a) (hab : a < b) (hα : 0 ≤ α)
    (hlo : ∀ w : M.coneIdealWordList C, lo ≤ M.coneIdealWordCost C s w)
    (hgap : (M.bound : ℝ) * α < (b - a) * lo)
    (t ε : ℝ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (ht : ∀ᶠ r in atTop, |t r| ≤ Real.exp ((α + ε r) * r)) :
    ∀ᶠ r in atTop,
      (fun g => Exp (t r • M.letter i) * g * (Exp (t r • M.letter i))⁻¹) ''
        M.coneIdealBox C (fun v => Exp v.val) (fun l => a * s l) β r 1 ⊆
      M.coneIdealBox C (fun v => Exp v.val) (fun l => b * s l) β r 1 := by
  filter_upwards [M.coneIdealLetterFlow_absorbed C b₀ s β hβ i hi ha hab hα
    hlo hgap t ε hε ht] with r hr
  rintro _ ⟨g, ⟨v, rfl, hv⟩, rfl⟩
  refine ⟨M.coneIdealLetterFlow C i (t r) v, ?_, hr v hv⟩
  exact M.coneIdealLetterFlow_exp_conjugation C Exp j ρ hρ hmatch i (t r) v

include hρ hmatch in
/-- The enlargement threshold is derived from the positive mixed widths,
independently of the time sequence and its vanishing envelope. -/
theorem exists_coneIdeal_conjugation_threshold
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (s : Fin M.letterCount → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hpos : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C → 0 < s i)
    (β : M.ConeIdealBases C) (hβ : M.IsMaximizingConeIdealBasis C b₀ s β)
    (i : Fin M.letterCount) (hi : s i = 0)
    {a b U : ℝ} (ha : 0 ≤ a) (hab : a < b) (hU : 0 < U) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ t ε : ℝ → ℝ, Tendsto ε atTop (𝓝 0) →
      (∀ᶠ r in atTop, |t r| ≤ Real.exp ((U * δ + ε r) * r)) →
      ∀ᶠ r in atTop,
        (fun g => Exp (t r • M.letter i) * g * (Exp (t r • M.letter i))⁻¹) ''
          M.coneIdealBox C (fun v => Exp v.val) (fun l => a * s l) β r 1 ⊆
        M.coneIdealBox C (fun v => Exp v.val) (fun l => b * s l) β r 1 := by
  obtain ⟨lo, hlo, hw⟩ := M.exists_positive_coneIdeal_width C s hs hpos
  let gap := (b - a) * lo
  let D := ((M.bound : ℝ) + 1) * U
  have hg : 0 < gap := mul_pos (sub_pos.mpr hab) hlo
  have hD : 0 < D := mul_pos (by positivity) hU
  let δ₀ := gap / (2 * D)
  have hδ₀ : 0 < δ₀ := div_pos hg (by positivity)
  have he : δ₀ * (2 * D) = gap := div_mul_cancel₀ gap (ne_of_gt (by positivity))
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hδle t ε hε ht
  apply M.coneIdeal_group_conjugation_absorbed C Exp j ρ hρ hmatch b₀ s β hβ i hi
    ha hab (mul_nonneg hU.le hδ.le) hw _ t ε hε ht
  have hstep : D * δ ≤ D * δ₀ := mul_le_mul_of_nonneg_left hδle hD.le
  calc
    (M.bound : ℝ) * (U * δ) ≤ D * δ := by dsimp [D]; nlinarith [mul_pos hU hδ]
    _ ≤ D * δ₀ := hstep
    _ < gap := by nlinarith

end PolycyclicRecognition.CartanWordModel

end

end OAI
