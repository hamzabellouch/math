import Mathlib.Basic.Complex.Basic

namespace OAI

namespace Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal
theorem normalize_guard_product (P : Prop) [Decidable P] (density amplitude jac kernel : ℂ) :
    density*(if P then (1:ℂ)*jac*amplitude*kernel else 0)=
      jac*((if P then (1:ℂ) else 0)*(density*(amplitude*kernel))) := by
  by_cases hP : P
  · simpa only [ite_eq_left hP,one_mul,mul_assoc] using
      (mul_left_comm density jac (amplitude*kernel))
  · simp only [ite_eq_right hP,mul_zero,zero_mul]

theorem normalize_guard_product_of_equalities (P : Prop) [Decidable P]
    (density amplitude jac kernel guard jac' kernel' : ℂ)
    (hg : guard=1) (hj : jac=jac') (hk : kernel=kernel') :
    density*(if P then guard*jac*amplitude*kernel else 0)=
      jac'*((if P then (1:ℂ) else 0)*(density*(amplitude*kernel'))) := by
  rw [hg,hj,hk]
  exact normalize_guard_product _ _ _ _ _

end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal

end OAI
