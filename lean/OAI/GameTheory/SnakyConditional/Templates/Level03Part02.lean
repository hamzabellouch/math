import OAI.GameTheory.SnakyConditional.Templates.Operations

namespace OAI

namespace SnakyConditional
def required_1 : Finset Cell := baseRequired 1
def envelope_1 : Finset Cell := baseEnvelope 1
theorem row_works_1 : Template HasSnaky 1 required_1 envelope_1 := base_works 1
end SnakyConditional

end OAI
