import OAI.Combinatorics.EditApproximation.Refinement.ComputedParameterRegisters
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalCoarsePreparation
import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseInputWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
open Filter MeasureTheory





theorem computedExecutionCoarsePreparationWork_integrable (source target : List ℕ) (N : ℕ) :
    Integrable (computedExecutionCoarsePreparationWork source target N) (computedExecutionLaw source target N) :=
  computedExecutionAcceptedWork_integrable source target N (computedFamilyCoarsePreparationWork source target N)

theorem computedExecutionCoarsePreparationWork_bound :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      (∀ a ∈ source ++ target, Nat.size a ≤ inputHeight N ^ 3) →
      ∀ execution : ComputedExecutionOutcome source target N,
      computedExecutionCoarsePreparationWork source target N execution ≤
        (inputHeight N : ℝ) ^ 6 * computedExecutionCoarseInputWork source target N execution := by
  filter_upwards [eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)] with N hN hell
  intro source target hsize hsymbol execution
  have hH : 100 ≤ inputHeight N := (by decide : 100 ≤ 256).trans
    (computed_coarse_height_large N (by omega) hell)
  have hl : Nat.size N ≤ inputHeight N + 1 :=
    (Nat.size_le_size (Nat.le_add_right N 2)).trans (inputLength_register_word N)
  have hp : inputHeight N + 1 ≤ inputHeight N ^ 3 := by
    have h : inputHeight N ≤ inputHeight N ^ 2 := Nat.le_pow (by decide)
    have hh := Nat.mul_le_mul_right (inputHeight N ^ 2) (show 2 ≤ inputHeight N by omega)
    nlinarith only [h, hh, hH]
  exact physicalFamilyCoarsePreparationWork_bound source target N (integerParameters N).P (inputHeight N)
    (integerParameters N).T (integerParameters N).S (computedSeedPassCount N) (inputHeight N ^ 2)
    (scheduledSeedFactor N) (scheduledSeedMultiplier N)
    (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).eta
    (rationalParameters (inputSmallLog N)).kappa (rationalParameters (inputSmallLog N)).delta
    (clampedSeedNat (computedExecutionAccepted source target N execution).1)
    (computedExecutionAccepted source target N execution).2 (16384 * inputHeight N + 5)
    (computedFamilyMemoCode source target N (inputHeight N ^ 2)) (computedFinalRoot source target N)
    hH ((Nat.size_le_size (by omega : source.length ≤ N)).trans (hl.trans hp))
    ((Nat.size_le_size (by omega : target.length ≤ N)).trans (hl.trans hp)) hsymbol

theorem computedExecutionCoarsePreparationWork_expected_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      (∀ a ∈ source ++ target, Nat.size a ≤ inputHeight N ^ 3) →
      (∫ execution, computedExecutionCoarsePreparationWork source target N execution
        ∂computedExecutionLaw source target N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  have he : 0 < epsilon / 2 := half_pos hepsilon
  filter_upwards [computedExecutionCoarsePreparationWork_bound,
    computedExecutionCoarseInputWork_expected_near_linear (epsilon / 2) he,
    fixed_height_power_subpolynomial 6 (epsilon / 2) he] with N hb hi hp
  intro source target hsize hsymbol
  have hm := integral_mono (computedExecutionCoarsePreparationWork_integrable source target N)
    ((computedExecutionCoarseInputWork_integrable source target N).const_mul ((inputHeight N : ℝ) ^ 6))
    (hb source target hsize hsymbol)
  rw [integral_const_mul] at hm
  calc
    _ ≤ (inputHeight N : ℝ) ^ 6 * (N + 2 : ℝ) ^ (1 + epsilon / 2) :=
      hm.trans (mul_le_mul_of_nonneg_left (hi source target hsize) (by positivity))
    _ ≤ (N + 2 : ℝ) ^ (epsilon / 2) * (N + 2 : ℝ) ^ (1 + epsilon / 2) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end EditApproximation

end OAI
