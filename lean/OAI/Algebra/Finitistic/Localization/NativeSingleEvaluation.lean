import OAI.Algebra.Finitistic.Localization.NativeProjectiveModel
import OAI.Algebra.Finitistic.Bimodule.BimoduleDerivedShift

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal.BoundedProjective
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {P : BiComplex k B} (data : BoundedProjective k B P)
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]

/-- Native degree-zero module embedding, with the module's original compatible scalar action. -/
def nativeSingleEvaluation (N : Type u) [AddCommGroup N] [Module k N] [Module B N]
    [IsScalarTower k B N] :
    data.derived.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B N)) ≅
      DerivedCategory.Q.obj (((BimoduleBalancedTensor.functor k B N).mapHomologicalComplex (.up ℤ)).obj P) :=
  data.nativeEvaluation N
end LittleFinitistic.BimoduleTotal.BoundedProjective

end

end OAI
