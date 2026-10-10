import OAI.Algebra.FormulaHitting.Hitting
import OAI.Algebra.FormulaHitting.FormulaBridge
import OAI.Algebra.FormulaHitting.GeneratorBridge

namespace OAI

namespace NCHitting

universe u

theorem complete_result : NCHittingSpecification.CompleteTheorem.{u} := by
  intro n s hn hs
  apply NCHittingSpecification.completeClaim_of_hitting hn hs
  intro F instField instCharZero f hsize hf
  have hi := NCHitting.universal_hitting n s hn hs F f.toImplementation
    (by simpa using hsize) (by simpa using hf)
  intro hz
  apply hi
  exact (f.toImplementation_eval (fun i => Matrix.of
    (fun r q => (NCHittingSpecification.expectedEntry n s i r q : F)))).trans hz

end NCHitting

end OAI
