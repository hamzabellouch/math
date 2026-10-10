import OAI.InformationTheory.BooleanNoise.PerspectiveCalculus
import OAI.InformationTheory.SoftChannel.PerspectiveLogTrapezoid

namespace OAI

section

noncomputable section

open Set

namespace LeanBlast.CourtadeKumar

theorem PerspectiveCalculus_hasDerivAt_const_quotient (x v : ℝ) (hv : 0 < v) :
    HasDerivAt (fun w : ℝ => x / w) (-x / v ^ 2) v := by
  convert! (hasDerivAt_const v x).div (hasDerivAt_id v) (ne_of_gt hv) using 1;
    simp

end LeanBlast.CourtadeKumar
end
end

end OAI
