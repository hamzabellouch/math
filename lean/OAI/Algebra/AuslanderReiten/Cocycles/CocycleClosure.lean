import OAI.Algebra.AuslanderReiten.Cocycles.CocycleFormula
import OAI.Algebra.AuslanderReiten.Cocycles.CocycleCertificate
import OAI.Algebra.AuslanderReiten.Cocycles.CocycleCorners

namespace OAI

namespace ArExplicit.CocycleData

variable {k : Type*} [Field k] [CharP k 2] (q : k)

theorem p_cocycle (a b c d : T k q) :
    a * p q b c d + p q (a * b) c d + p q a (b * c) d +
      p q a b (c * d) + p q a b c * d = 0 := by
  rw [p_differential_formula]
  exact differentialTerms_sum_zero (SparseParity.module_add_self_eq_zero (k := k)) _

omit [CharP k 2] in

theorem p_detecting_cycle_ne_zero (hq : q ≠ 0) :
    q ^ 2 • p q (T.vector q (false, .t)) (T.vector q (false, .x)) (T.vector q (true, .j)) +
      p q (T.vector q (false, .t)) (T.vector q (false, .y)) (T.vector q (true, .j)) ≠ 0 := by
  rw [p_detecting_cycle]
  intro hz
  have hh := congrArg (T.coefficient q (false, .f)) hz
  have hq3 : q ^ 3 ≠ 0 := pow_ne_zero 3 hq
  apply hq3
  simpa using hh

end ArExplicit.CocycleData

end OAI
