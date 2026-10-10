import OAI.Algebra.Finitistic.Ordinary.OrdinaryBlockBimodule
import OAI.Algebra.Finitistic.Ordinary.OrdinaryAssociativeTensorModules

namespace OAI
noncomputable section
namespace LittleFinitistic.BlockModule
universe u
/-- A module supported on the first factor of the actual product algebra. -/
def First (_k _L _R Z : Type u) := Z
/-- A module supported on the second factor of the actual product algebra. -/
def Second (_k _L _R Z : Type u) := Z
variable (k L R Z : Type u) [Field k] [Ring L] [Ring R] [Algebra k L] [Algebra k R]
  [AddCommGroup Z] [Module k Z]
namespace First
instance : AddCommGroup (First k L R Z) := inferInstanceAs (AddCommGroup Z)
instance : Module k (First k L R Z) := inferInstanceAs (Module k Z)
instance [Module L Z] : Module (L × R) (First k L R Z) := Module.compHom Z (RingHom.fst L R)
instance [Module L Z] [IsScalarTower k L Z] : IsScalarTower k (L × R) (First k L R Z) where
  smul_assoc c d z := smul_assoc c d.1 (show Z from z)
end First
namespace Second
instance : AddCommGroup (Second k L R Z) := inferInstanceAs (AddCommGroup Z)
instance : Module k (Second k L R Z) := inferInstanceAs (Module k Z)
instance [Module R Z] : Module (L × R) (Second k L R Z) := Module.compHom Z (RingHom.snd L R)
instance [Module R Z] [IsScalarTower k R Z] : IsScalarTower k (L × R) (Second k L R Z) where
  smul_assoc c d z := smul_assoc c d.2 (show Z from z)
end Second
end LittleFinitistic.BlockModule

end

end OAI
