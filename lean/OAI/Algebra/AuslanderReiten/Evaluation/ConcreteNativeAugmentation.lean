import OAI.Algebra.AuslanderReiten.Evaluation.RegularEvaluatedAugmentation
import OAI.Algebra.AuslanderReiten.Ext.ExternalNativeBarAugmentation
import OAI.Algebra.AuslanderReiten.Bar.ConcreteNativeBar
import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteBaseAugmentation

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "T₀" => T k q
local notation "A₀" => A k q
local notation "S" => Resolution.Simple q
local notation "D" => bimoduleTwoConeData q
local notation "hf" => bimodule_term_finite_k q
local notation "X" => A.simpleFiniteModule q
local instance : Module k (canonicalTensorSimple q) :=
  moduleCatBaseModule (k := k) (R := A₀) (canonicalTensorSimple q)
local instance : IsScalarTower k A₀ (canonicalTensorSimple q) :=
  moduleCatBaseTower (k := k) (R := A₀) (canonicalTensorSimple q)
local instance : Module k (AbsoluteBar.moduleObject k A₀ 0) :=
  moduleCatBaseModule (k := k) (R := A₀ ⊗[k] A₀ᵐᵒᵖ) (AbsoluteBar.moduleObject k A₀ 0)
local instance : IsScalarTower k (A₀ ⊗[k] A₀ᵐᵒᵖ) (AbsoluteBar.moduleObject k A₀ 0) :=
  moduleCatBaseTower (k := k) (R := A₀ ⊗[k] A₀ᵐᵒᵖ) (AbsoluteBar.moduleObject k A₀ 0)

private abbrev nativeEvaluation := EnvelopingBimodule.evaluationFunctor k A₀ (X).carrier
private abbrev canonicalEvaluation := EnvelopingBimodule.evaluationFunctor k A₀ (canonicalTensorSimple q)

def simpleRegularEndpoint : (nativeEvaluation q).obj (AbsoluteBar.moduleObject k A₀ 0) ⟶
    canonicalTensorSimple q :=
  BarBalanced.endpointWithCoefficients k A₀ (X).carrier (canonicalTensorSimple q)
    (nativeToCanonicalSimple q)

theorem simpleBaseAugmentation :
    (nativeEvaluation q).map (bimoduleAugmentation q) ≫ simpleRegularEndpoint q =
      (simpleOrdinaryResolution q).π.f 0 ≫
        (evaluatedBaseZeroEquiv q).toModuleIso.hom ≫ (nativeToCanonicalSimple q).hom := by
  let f : (D).term 0 ⟶ (TwoCone.baseCokernelModule D hf 0).carrier :=
    ConcreteCategory.ofHom (C := ModuleCat (A₀ ⊗[k] A₀ᵐᵒᵖ)) (LinearMap.range ((D).d 0)).mkQ
  have hb : f ≫ (bimoduleBaseCokernelEquiv q).toModuleIso.hom = bimoduleAugmentation q := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact bimoduleBaseCokernelEquiv_mk q
  have h := BarBalanced.regularEvaluatedAugmentation k A₀ (X).carrier
    (canonicalTensorSimple q) ((D).term 0) (TwoCone.baseCokernelModule D hf 0).carrier
    (nativeToCanonicalSimple q) f (bimoduleBaseCokernelEquiv q) (bimoduleAugmentation q) hb
  change (nativeEvaluation q).map (bimoduleAugmentation q) ≫ simpleRegularEndpoint q =
    (TwoCone.evaluatedOrdinaryAugmentation D hf X).f 0 ≫ _
  rw [TwoCone.evaluatedOrdinaryAugmentation_zero]
  exact h

end ArExplicit.T

end

end OAI
