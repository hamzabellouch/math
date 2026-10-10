import OAI.Probability.MatroidSecretary.Pivots.MarkedQueryProgramModel

namespace OAI

/-! Execution-local freshness for adaptive transaction policies. -/

namespace MatroidProphet.MarkedQueryProgram

variable {α : Type*} [DecidableEq α]

/-- Only the actually followed branch must query each available label at most once.
This makes no assertion about branches impossible under the chosen bit law. -/
def FreshAt (S : Finset α) : MarkedQueryProgram α → Finset α → Prop
  | .stop, _ => True
  | .query e no yes, V => e ∈ V ∧
      if e ∈ S then yes.FreshAt S (V.erase e) else no.FreshAt S (V.erase e)
  | .finish _ rest, V => rest.FreshAt S V

end MatroidProphet.MarkedQueryProgram

end OAI
