import OAI.Geometry.CylinderCovering.Ruled.C1Definitions

namespace OAI

noncomputable section
namespace RuledApproximation.NilpotentDomainExample

def field (p : Plane) : Plane := p 1 • vec2 1 0 + (p 0)^3 • vec2 0 1

def labels : Set Plane := (fun y : ℝ => vec2 0 y) '' Set.Icc (-1 : ℝ) 1

end RuledApproximation.NilpotentDomainExample

end

end OAI
