import OAI.GameTheory.SnakyConditional.Templates.Operations

namespace OAI

namespace SnakyConditional
def required_3 : Finset Cell := baseRequired 3
def envelope_3 : Finset Cell := baseEnvelope 3
theorem row_works_3 : Template HasSnaky 1 required_3 envelope_3 := base_works 3
end SnakyConditional

end OAI
