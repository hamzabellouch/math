import OAI.Algebra.AuslanderReiten.Fibers.ExplicitBimoduleFiber

namespace OAI

noncomputable section
namespace ArExplicit.T
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)

instance explicitBimodule_finite_left : Module.Finite (A k q) (explicitBimodule q H₁ H₂) :=
  (explicitBimodule_left q H₁ H₂).1

instance explicitBimodule_projective_left : Module.Projective (A k q) (explicitBimodule q H₁ H₂) :=
  (explicitBimodule_left q H₁ H₂).2

instance explicitBimodule_finite_right : Module.Finite (A k q)ᵐᵒᵖ (explicitBimodule q H₁ H₂) :=
  (explicitBimodule_right q H₁ H₂).1

instance explicitBimodule_projective_right : Module.Projective (A k q)ᵐᵒᵖ (explicitBimodule q H₁ H₂) :=
  (explicitBimodule_right q H₁ H₂).2

end ArExplicit.T

end

end OAI
