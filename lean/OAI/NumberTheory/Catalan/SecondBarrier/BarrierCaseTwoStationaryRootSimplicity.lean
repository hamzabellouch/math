import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoMaxReduction

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem barrierCase2X_stationary_numerator_simple {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1)
    (hstat : deriv barrierCase2X x = 0) :
    (barrierCase2AX.map (Rat.castHom ℝ)).rootMultiplicity x = 1 := by
  have hi : x ∈ Set.Ioo (-1 : ℝ) 1 := by
    rcases hx with hn | hp
    · exact ⟨hn.1, hn.2.trans (by norm_num)⟩
    · exact ⟨(by norm_num : (-1 : ℝ) < 0).trans hp.1, hp.2⟩
  have h0 : x ≠ 0 := by
    rcases hx with hn | hp
    · exact ne_of_lt hn.2
    · exact ne_of_gt hp.1
  exact barrierCase2AX_rootMultiplicity_eq_one hx
    ((barrierCase2X_deriv_eq_zero_iff hi h0).mp hstat)

theorem barrierCase2Y_stationary_numerator_simple {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hstat : deriv barrierCase2Y x = 0) :
    (barrierCase2AY.map (Rat.castHom ℝ)).rootMultiplicity x = 1 := by
  exact barrierCase2AY_rootMultiplicity_eq_one hx
    ((barrierCase2Y_deriv_eq_zero_iff hx).mp hstat)

end InternalCatalan

end

end

end OAI
