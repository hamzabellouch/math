import OAI.GameTheory.SnakyConditional.Templates.Operations

namespace OAI

namespace SnakyConditional
def required_2 : Finset Cell := baseRequired 2
def envelope_2 : Finset Cell := baseEnvelope 2
theorem row_works_2 : Template HasSnaky 1 required_2 envelope_2 := base_works 2
end SnakyConditional

end OAI
