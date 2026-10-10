import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeTailParameters
import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeAllWeights

namespace OAI

noncomputable section
open Filter
namespace LipschitzHilbert

theorem amplitudeTailCoefficient_pos : 0<(8:ℝ)+2*(2/(1-(Real.sqrt 2)⁻¹)) := by
  have hd : 0<1-(Real.sqrt 2)⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ Real.one_lt_sqrt_two)
  positivity

theorem amplitudeTailCost_nonneg (Q L : ℝ) (hQ : 0≤Q) : 0≤amplitudeTailCost Q L := by
  unfold amplitudeTailCost
  exact mul_nonneg (mul_nonneg amplitudeTailCoefficient_pos.le hQ) (Real.exp_pos _).le

theorem retainedAmplitudeCost_nonneg (C L : ℝ) : 0≤retainedAmplitudeCost C L := by
  unfold retainedAmplitudeCost
  positivity

theorem eventually_amplitudeTailCost_bound (A B : ℝ) (hA : 0<A) (hB : 0≤B) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℝ, Q≤A*Real.exp (B*L^(9/10:ℝ)) →
      amplitudeTailCost Q L≤Real.exp (-L/16) :=
  eventually_amplitude_tail_decay A B _ hA hB amplitudeTailCoefficient_pos

end LipschitzHilbert

end

end OAI
