import Mathlib
import OAI.Combinatorics.UniformKServer.PilotCompact

namespace OAI

                                     
section
namespace UniformKServer.PilotCompact
noncomputable section
variable {X Ω : Type*} [Fintype X] [MetricSpace X] [Fintype Ω]

def minimizer (r σ R : ℝ) (μ g : X → ℝ) : X → ℝ :=
  Classical.choose (minimum_exists r σ R μ g)

theorem minimizer_feasible (r σ R : ℝ) (μ g : X → ℝ) :
    feasible r σ R (minimizer r σ R μ g) :=
  (Classical.choose_spec (minimum_exists r σ R μ g)).1

theorem minimizer_value (r σ R : ℝ) (μ g : X → ℝ) :
    objective r σ R μ g (minimizer r σ R μ g) = value r σ R μ g :=
  (Classical.choose_spec (minimum_exists r σ R μ g)).2.1

/-- The old template is measurable before the edit decision. In particular,
this theorem is never conditional on the event that an edit is selected. -/
theorem filtering (r σ R : ℝ) (w : Ω → ℝ) (F : Setoid Ω)
    (μold μminus g : Ω → X → ℝ)
    (hw : ∀ ω, 0 ≤ w ω)
    (hμ : ∀ ω ω', F.r ω ω' → μold ω = μold ω')
    (hg : ∀ ω ω', F.r ω ω' → g ω = g ω')
    (hfilter : ∀ (a : Ω → ℝ), (∀ ω ω', F.r ω ω' → a ω = a ω') →
      ∀ y, (∑ ω, w ω * a ω * (μminus ω y - μold ω y)) = 0) :
    (∑ ω, w ω * value r σ R (μminus ω) (g ω)) ≤
      ∑ ω, w ω * value r σ R (μold ω) (g ω) := by
  let z := fun ω => minimizer r σ R (μold ω) (g ω)
  have hmeas : ∀ y ω ω', F.r ω ω' →
      integrand r σ R (g ω) (z ω) y = integrand r σ R (g ω') (z ω') y := by
    intro y ω ω' h
    dsimp [z]
    rw [hμ ω ω' h,hg ω ω' h]
  have heq : (∑ ω, w ω * objective r σ R (μminus ω) (g ω) (z ω)) =
      ∑ ω, w ω * objective r σ R (μold ω) (g ω) (z ω) := by
    apply sub_eq_zero.mp
    rw [←Finset.sum_sub_distrib]
    have hx : ∀ ω, w ω*objective r σ R (μminus ω) (g ω) (z ω)-
        w ω*objective r σ R (μold ω) (g ω) (z ω) =
          r*∑ y, w ω*integrand r σ R (g ω) (z ω) y*(μminus ω y-μold ω y) := by
      intro ω
      simp only [objective,Finset.mul_sum,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y _
      ring
    simp_rw [hx]
    rw [←Finset.mul_sum,Finset.sum_comm]
    have hz : ∀ y, (∑ ω, w ω*integrand r σ R (g ω) (z ω) y*(μminus ω y-μold ω y)) = 0 :=
      fun y => hfilter _ (hmeas y) y
    simp only [hz,Finset.sum_const_zero,mul_zero]
  calc
    _ ≤ ∑ ω, w ω*objective r σ R (μminus ω) (g ω) (z ω) :=
      Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
        (value_le r σ R (μminus ω) (g ω) (z ω) (minimizer_feasible ..)) (hw ω)
    _ = ∑ ω, w ω*objective r σ R (μold ω) (g ω) (z ω) := heq
    _ = _ := by simp only [z,minimizer_value]

end
end UniformKServer.PilotCompact

end



end OAI
