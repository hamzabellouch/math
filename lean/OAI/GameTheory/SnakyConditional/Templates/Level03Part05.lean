import OAI.GameTheory.SnakyConditional.Templates.Operations

namespace OAI

namespace SnakyConditional
def required_4 : Finset Cell := baseRequired 4
def envelope_4 : Finset Cell := baseEnvelope 4
theorem row_works_4 : Template HasSnaky 1 required_4 envelope_4 := base_works 4
end SnakyConditional

end OAI
