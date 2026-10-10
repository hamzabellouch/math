import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteEvaluatedBase
import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedBaseShift
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorAugmentation

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "T₀" => T k q
local notation "A₀" => A k q
local notation "D" => bimoduleTwoConeData q

def bimoduleAugmentation : (D).term 0 ⟶ AbsoluteBar.moduleObject k A₀ 0 :=
  (ExternalTensor.envelopingFunctor k T₀ T₀).map ((tensorBarResolution q).π.f 0) ≫
    (barTensorZeroEquiv k T₀ T₀).toModuleIso.hom

theorem bimoduleBaseCokernelEquiv_mk (x : (D).term 0) :
    bimoduleBaseCokernelEquiv q (Submodule.Quotient.mk x) = (bimoduleAugmentation q).hom x := rfl

theorem simpleOrdinaryBarIso_f (n : ℕ) :
    (simpleOrdinaryBarIso q).hom.f n = 𝟙 ((simpleOrdinaryResolution q).complex.X n) := by
  change (EnvelopingBimodule.evaluationFunctor k A₀ (A.simpleFiniteModule q).carrier).map
    (𝟙 ((D).term n)) = _
  exact CategoryTheory.Functor.map_id _ _

end ArExplicit.T

end

end OAI
