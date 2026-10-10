import OAI.GameTheory.SnakyConditional.Templates.Operations

namespace OAI

namespace SnakyConditional
def required_5 : Finset Cell := baseRequired 5
def envelope_5 : Finset Cell := baseEnvelope 5
theorem row_works_5 : Template HasSnaky 1 required_5 envelope_5 := base_works 5
end SnakyConditional

end OAI
