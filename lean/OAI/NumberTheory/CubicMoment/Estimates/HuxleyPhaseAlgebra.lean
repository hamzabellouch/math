import OAI.NumberTheory.CubicMoment.Estimates.HuxleyPhase

namespace OAI

/-! Phase multiplication for the Gaussian Gram expansion. -/
noncomputable section
namespace CubicFirstMoment

lemma norm_huxleyFrequencyPhase (x : ℂ) (n : Eisenstein) :
    ‖huxleyFrequencyPhase x n‖ = 1 := Circle.norm_coe _

lemma huxleyFrequencyPhase_sub (x y : ℂ) (n : Eisenstein) :
    huxleyFrequencyPhase (x-y) n =
      huxleyFrequencyPhase x n*star (huxleyFrequencyPhase y n) := by
  have he : tracePair (n:ℂ) ((x-y)/traceLambda) =
      tracePair (n:ℂ) (x/traceLambda)-tracePair (n:ℂ) (y/traceLambda) := by
    simp only [tracePair,sub_div,mul_sub,Complex.sub_re]
  unfold huxleyFrequencyPhase
  rw [he,sub_eq_add_neg,AddChar.map_add_eq_mul,Circle.coe_mul,
    AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj]
  rfl

end CubicFirstMoment

end

end OAI
