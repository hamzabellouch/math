import OAI.Algebra.Finitistic.Bimodule.BimoduleTensorVertexBridge
import OAI.Algebra.Finitistic.Localization.NativeArrowBridge

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.TensorArrowComparison
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (N : Type u) [AddCommGroup N] [Module k N] [Module B N]

/-- Tensor the actual right vertex, then identify it with the vertex of the full
left B-module tensor, preserving the original balanced tensor classes. -/
def component (e : B) (he : e*e=e) (M : ModuleCat.{u} (Enveloping k B)) :
    (BalancedTensor.tensorFunctor k B N).obj ((BimoduleVertex.functor k B e).obj M) ≅
      (LeftVertexHomology.vertex k B e).obj ((BimoduleBalancedTensor.functor k B N).obj M) :=
  (BalancedVertexImage.equiv k B M e he N).toModuleIso ≪≫
    (BimoduleTensorVertexBridge.equiv k B N e M).symm.toModuleIso

/-- The tensor/vertex comparison retains left multiplication by every original
supported arrow, and does not require the evaluation module to be flat. -/
theorem arrow_square (ei ej a : B) (hi : ei*ei=ei) (hj : ej*ej=ej) (ha : ej*a=a)
    (M : ModuleCat.{u} (Enveloping k B)) :
    (BalancedTensor.tensorFunctor k B N).map
        ((ArrowVertex.arrow k B ei ej a ha).app M) ≫ (component k B N ej hj M).hom =
      (component k B N ei hi M).hom ≫
        (LeftVertexHomology.arrow k B ei ej a ha).app ((BimoduleBalancedTensor.functor k B N).obj M) := by
  let l := ((BalancedTensor.tensorFunctor k B N).map
    ((ArrowVertex.arrow k B ei ej a ha).app M) ≫ (component k B N ej hj M).hom).hom
  let r := ((component k B N ei hi M).hom ≫
    (LeftVertexHomology.arrow k B ei ej a ha).app
      ((BimoduleBalancedTensor.functor k B N).obj M)).hom
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change l x = r x
  induction x using BalancedTensor.induction_on with
  | hz => exact l.map_zero.trans r.map_zero.symm
  | ht m n => rfl
  | ha x y hx hy =>
    exact (l.map_add x y).trans ((congrArg₂ (· + ·) hx hy).trans (r.map_add x y).symm)

/-- Natural comparison for the full B-valued tensor functor. -/
def comparison (e : B) (he : e*e=e) :
    BimoduleVertex.functor k B e ⋙ BalancedTensor.tensorFunctor k B N ≅
      BimoduleBalancedTensor.functor k B N ⋙ LeftVertexHomology.vertex k B e :=
  BalancedVertexFunctor.comparison k B e he N ≪≫
    (BimoduleTensorVertexBridge.comparison k B N e).symm

def complexIso (e : B) (he : e*e=e) (P : BiComplex k B) :
    (((BalancedTensor.tensorFunctor k B N).mapHomologicalComplex (.up ℤ)).obj
      (((BimoduleVertex.functor k B e).mapHomologicalComplex (.up ℤ)).obj P)) ≅
    (((LeftVertexHomology.vertex k B e).mapHomologicalComplex (.up ℤ)).obj
      (((BimoduleBalancedTensor.functor k B N).mapHomologicalComplex (.up ℤ)).obj P)) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => component k B N e he (P.X n))
    (fun n m _ => ((comparison k B N e he).hom.naturality (P.d n m)).symm)

/-- The full chain comparison respects the original left multiplication arrows. -/
theorem complex_arrow_square (ei ej a : B) (hi : ei*ei=ei) (hj : ej*ej=ej) (ha : ej*a=a)
    (P : BiComplex k B) :
    ((BalancedTensor.tensorFunctor k B N).mapHomologicalComplex (.up ℤ)).map
        (ArrowVertex.arrowComplex k B ei ej a ha P) ≫ (complexIso k B N ej hj P).hom =
      (complexIso k B N ei hi P).hom ≫
        ((LeftVertexHomology.arrow k B ei ej a ha).mapHomologicalComplex (.up ℤ)).app
          (((BimoduleBalancedTensor.functor k B N).mapHomologicalComplex (.up ℤ)).obj P) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact arrow_square k B N ei ej a hi hj ha (P.X n)
end LittleFinitistic.TensorArrowComparison

end

end OAI
