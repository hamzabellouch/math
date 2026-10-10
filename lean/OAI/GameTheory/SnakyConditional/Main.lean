import OAI.GameTheory.SnakyConditional.OriginalResult
import OAI.GameTheory.SnakyConditional.Templates.Level03Part06

namespace OAI

namespace SnakyConditional

theorem conditional_templates :
    Template HasSnaky 19 required_557 envelope_557 ∧
    Template HasSnaky 27 required_595 envelope_595 ∧
    Template HasSnaky 27 required_603 envelope_603 ∧
    Template HasSnaky 34 required_615 envelope_615 := by
  exact ⟨row_works_557, row_works_595, row_works_603, row_works_615⟩

end SnakyConditional

end OAI
