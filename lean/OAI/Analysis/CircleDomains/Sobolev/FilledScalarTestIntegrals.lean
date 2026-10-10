import OAI.Analysis.CircleDomains.Sobolev.FilledScalarL2
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

namespace OAI

/-! All test-function pairings for the finite scalar fillings are actual
integrable functions on the whole plane. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 theorem eventually_filled_test_integrals (i : Fin m) :
    ∀ᶠ n in atTop, ∀ F : R.HoleFilling i n, ∀ φ : ℂ → ℝ,
      ContDiff ℝ 1 φ → HasCompactSupport φ →
      Integrable (fun z => F.filled z * fderiv ℝ φ z 1) ∧
      Integrable (fun z => fderiv ℝ F.filled z 1 * φ z) ∧
      Integrable (fun z => F.filled z * fderiv ℝ φ z Complex.I) ∧
      Integrable (fun z => fderiv ℝ F.filled z Complex.I * φ z) := by
  filter_upwards [R.eventually_filled_partials_memLp i] with n hn F φ hφ hs
  have hF : ∀ᵐ z ∂(volume : Measure ℂ), ‖F.filled z‖ ≤ (1 : ℝ) :=
    Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (F.filled_mem z).1]
      exact (F.filled_mem z).2
  have hc (v : ℂ) : Continuous (fun z => fderiv ℝ φ z v) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have ht (v : ℂ) : Integrable (fun z => F.filled z * fderiv ℝ φ z v) :=
    ((hc v).integrable_of_hasCompactSupport (hs.fderiv_apply (𝕜 := ℝ) v)).bdd_mul
      F.filled_measurable.aestronglyMeasurable hF
  have hφ₂ : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hs
  exact ⟨ht 1, (hn F).1.integrable_mul hφ₂, ht Complex.I, (hn F).2.integrable_mul hφ₂⟩

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
