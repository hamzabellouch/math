import OAI.Dynamics.EntropyCounterexample.PeriodicEntropy

namespace OAI

noncomputable section

namespace Problem340
namespace ClockAtInfinity

abbrev Clock := AddCircle (100 : ℝ)

def step (t : Clock) : Clock := t + ((1 : ℝ) : Clock)

@[continuity, fun_prop]
theorem continuous_step : Continuous step :=
  continuous_id.add continuous_const

theorem step_period : step^[100] = id := by
  have h : (100 : ℕ) • ((1 : ℝ) : Clock) = 0 := by
    rw [← AddCircle.coe_nsmul]
    norm_num [nsmul_eq_mul]
  funext t
  change (fun x : Clock => x + ((1 : ℝ) : Clock))^[100] t = t
  rw [add_right_iterate]
  simp only [h, add_zero]

theorem coverEntropy_step : Dynamics.coverEntropy step (Set.univ : Set Clock) = 0 := by
  let : Fact (0 < (100 : ℝ)) := ⟨by norm_num⟩
  exact PeriodicEntropy.coverEntropy_eq_zero_of_period (by norm_num) step_period

theorem coverEntropy_clockImage {X : Type*} [UniformSpace X]
    {T : X → X} {φ : Clock → X} (hφ : Continuous φ)
    (hsem : Function.Semiconj φ step T) :
    Dynamics.coverEntropy T (Set.range φ) = 0 := by
  let : Fact (0 < (100 : ℝ)) := ⟨by norm_num⟩
  apply le_antisymm _ (Dynamics.coverEntropy_nonneg T (Set.range_nonempty φ))
  have h := Dynamics.coverEntropy_image_le_of_uniformContinuous hsem
    (CompactSpace.uniformContinuous_of_continuous hφ) Set.univ
  simpa only [Set.image_univ, coverEntropy_step] using h

end ClockAtInfinity
end Problem340

end

end OAI
