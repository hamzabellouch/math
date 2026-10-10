import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationBlockDefs

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected
open HistorySignedResidueFactorization
attribute [local instance] Classical.propDecidable

theorem guarded_kernel_scalar (P : Prop)
    (m d v k d' v' k' : ℂ)
    (hm : m=guardIndicator P) (hd : d=d') (hv : v=v') (hk : k=k') :
    m*(d*(v*k))=k'*(d'*(if true ∧ ¬P then 0 else v')) := by
  subst m d v k
  by_cases h : P
  · simp only [guardIndicator,h,not_true_eq_false,and_false,ite_false,ite_true,one_mul]
    ring
  · simp only [guardIndicator,h,not_false_eq_true,and_true,ite_true,ite_false,zero_mul,mul_zero]

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

end

end OAI
