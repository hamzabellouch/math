import Mathlib
import OAI.Analysis.Conductivity.Walls.EndingJoinCutoff

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma delayedEndingTensor_periodic (lam J L K R : ℝ) (k : ℤ) :
    AngularPeriodic (2*Real.pi) (delayedEndingTensor lam k J L K R) := by
  intro n x
  change alignedEndingTensor lam k J L K (x+angularShift (2*Real.pi) n-Pi.single 0 R)=_
  rw [add_sub_right_comm,alignedEndingTensor_angularPeriodic]
  rfl

lemma endingJoinTensor_periodic {D : Coord3 → Mat3}
    (hD : AngularPeriodic (2*Real.pi) D) (lam J L K : ℝ) (k : ℤ) :
    AngularPeriodic (2*Real.pi) (endingJoinTensor D lam k J L K) := by
  intro n x
  have ht : (x+angularShift (2*Real.pi) n) 0=x 0 := by simp [angularShift]
  simp only [endingJoinTensor,ht,hD n x,delayedEndingTensor_periodic _ _ _ _ _ _ n x]

end ScalarConductivity

end
end

end OAI
