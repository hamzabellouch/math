import OAI.Algebra.AuslanderReiten.Tensor.TwistedEnvelopingFunctor

namespace OAI

noncomputable section
namespace ArExplicit
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (σ : R ≃ₐ[k] R)

instance twistedEnveloping_left_finite :
    Module.Finite R (EnvelopingBimodule k R (twistedFiniteModule σ).carrier) := by
  let := (twistedFiniteModule_left σ).1
  infer_instance

instance twistedEnveloping_left_projective :
    Module.Projective R (EnvelopingBimodule k R (twistedFiniteModule σ).carrier) := by
  let := (twistedFiniteModule_left σ).2
  infer_instance

instance twistedEnveloping_right_finite :
    Module.Finite Rᵐᵒᵖ (EnvelopingBimodule k R (twistedFiniteModule σ).carrier) := by
  let := (twistedFiniteModule_right σ).1
  infer_instance

instance twistedEnveloping_right_projective :
    Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R (twistedFiniteModule σ).carrier) := by
  let := (twistedFiniteModule_right σ).2
  infer_instance

end ArExplicit

end

end OAI
