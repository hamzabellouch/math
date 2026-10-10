import OAI.Probability.ClassicalON.PeriodicODE

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem potential_partition_ratio (S : SpinSystem 3 V E) (f : V → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hP : ∀ x s, S.pin x=some s → f x=0 ∨ f x=1)
    (hR : ∀ t, -(S.rotatePotential f t).secondAxisResponse (S.differential f) (S.differential f) ≤ δ)
    (x y : ℝ) :
    1-δ*(2*Real.pi)^2/2 ≤ (S.rotatePotential f x).Z (fun _ => 1) /
      (S.rotatePotential f y).Z (fun _ => 1) := by
  let A := S.potentialOperators f
  let F := fun t : ℝ => S.Z (fun e => NormedSpace.exp (t • A e))
  let F' := fun t => ∫ σ, S.firstWeight A t σ ∂S.reference
  let F'' := fun t => ∫ σ, S.secondWeight A t σ ∂S.reference
  have hZ (t : ℝ) : F t=(S.rotatePotential f t).Z (fun _ => 1) := by
    have h := S.potential_shift_Z f t 0
    simpa only [add_zero,zero_smul ℝ (S.potentialOperators f _),NormedSpace.exp_zero] using h
  have hper : Function.Periodic F (2*Real.pi) := by
    intro t
    rw [hZ,hZ,S.rotatePotential_periodic f hP t]
  have hpos (t : ℝ) : 0<F t := S.Z_pos _
  have hode (t : ℝ) : -(δ*F t) ≤ F'' t := by
    have hr := hR t
    rw [← S.potential_second_response] at hr
    change -(F'' t/F t) ≤ δ at hr
    rw [← neg_div,div_le_iff₀ (hpos t)] at hr
    linarith
  have h := ClassicalON.periodic_ode_ratio F F' F'' (2*Real.pi) δ (by positivity) hδ
    hper hpos (S.hasDerivAt_twistZ A) (S.hasDerivAt_firstVariation A) hode x y
  simpa only [hZ] using h

end ClassicalON.SpinSystem

end

end OAI
