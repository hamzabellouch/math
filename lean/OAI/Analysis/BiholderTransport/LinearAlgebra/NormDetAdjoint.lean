import Mathlib

namespace OAI

section
noncomputable section
namespace WeakMTWTransport
lemma normDet_adjoint_of_pos {E F:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [CompleteSpace E] [CompleteSpace F]
    (T:E →L[ℝ] F) (hd:Module.finrank ℝ E=Module.finrank ℝ F)
    (hT:0 < T.toLinearMap.normDet) :
    T.adjoint.toLinearMap.normDet=T.toLinearMap.normDet := by
  have hm:=LinearMap.normDet_comp_of_finrank_eq T.toLinearMap T.adjoint.toLinearMap hd
  have hs:(T.adjoint.comp T).det=T.toLinearMap.normDet^2:=by
    simpa only [RCLike.ofReal_real_eq_id,id_eq] using T.normDet_sq.symm
  rw [LinearMap.normDet_eq_abs_det] at hm
  change |(T.adjoint.comp T).det|=T.adjoint.toLinearMap.normDet*T.toLinearMap.normDet at hm
  rw [hs,abs_of_nonneg (sq_nonneg _),pow_two] at hm
  exact (mul_right_cancel₀ hT.ne' hm).symm
end WeakMTWTransport

end
end

end OAI
