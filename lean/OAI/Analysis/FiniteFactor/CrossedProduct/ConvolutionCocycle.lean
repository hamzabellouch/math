import OAI.Analysis.FiniteFactor.CrossedProduct.Cocycle
import OAI.Analysis.FiniteFactor.Convolution

namespace OAI

namespace FiniteFactor
open MeasureTheory
noncomputable section

/-- The actual cocycle is antitone in every integer index, including negative indices. -/
theorem sourceCocycle_antitone {ι : Type*} (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    {x : ι → ℝ} (hx : finiteFloorSupport θ x) :
    Antitone (fun k : ℤ => sourceCocycle θ c k x) := by
  intro k l hkl
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply (sourceLog_summable θ c hx k).tsum_le_tsum _ (sourceLog_summable θ c hx l)
  intro i
  apply mul_le_mul_of_nonneg_left _ (hc i)
  have hh : coordinateFloor θ k x i ≤ coordinateFloor θ l x i := by
    apply Int.floor_mono
    apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkl) (hθ i)
  exact_mod_cast hh

/-- Exact positive-power weight in terms of the two integer cocycle values. -/
theorem sourceCocycle_power_weight {ι : Type*} (θ c : ι → ℝ)
    {x : ι → ℝ} (hx : finiteFloorSupport θ x) (n : ℕ) (k : ℤ) :
    sourceCocycle θ c n (coordinateRotate θ k x) =
      sourceCocycle θ c ((n : ℤ)+k) x / sourceCocycle θ c k x := by
  rw [add_comm (n : ℤ) k,sourceCocycle_add θ c hx]
  exact (mul_div_cancel_right₀ _ (ne_of_gt (sourceCocycle_pos θ c k x))).symm

end
end FiniteFactor

end OAI
