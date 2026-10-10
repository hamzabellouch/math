import OAI.Algebra.AuslanderReiten.Cocycles.CocycleClosure
import OAI.Algebra.AuslanderReiten.Cocycles.CocycleDetector

namespace OAI

noncomputable section
namespace ArExplicit.CocycleData

variable {k : Type*} [Field k] [CharP k 2] (q : k)

theorem p_isCocycle3 : AbsoluteBar.IsCocycle3 k (T k q) (p q) := by
  intro a b c d
  have h := @p_cocycle k inferInstance inferInstance q a b c d
  convert! h using 1

def simpleExtClass : CategoryTheory.Abelian.Ext
    (ModuleBar.moduleObject k (T k q) (Resolution.Simple q) 0)
    (ModuleBar.moduleObject k (T k q) (Resolution.Simple q) 0) 3 :=
  ModuleBar.extClass3 k (T k q) (Resolution.Simple q) (p q) (p_isCocycle3 q)

theorem simpleExtClass_ne_zero (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    simpleExtClass q ≠ 0 :=
  ModuleBar.extClass3_ne_zero_of_detector k (T k q) (Resolution.Simple q)
    (p q) (p_isCocycle3 q) (detector q) (detector_evaluation_ne_zero q hq hq1)
    (detector_boundary q hq1)

end ArExplicit.CocycleData

end

end OAI
