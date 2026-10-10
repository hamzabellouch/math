import OAI.Algebra.AuslanderReiten.Bar.ExternalBarEvaluation
import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteEvaluationCoefficient

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "T₀" => T k q
local notation "A₀" => A k q
local notation "S" => Resolution.Simple q
local notation "D" => bimoduleTwoConeData q
local notation "hf" => bimodule_term_finite_k q
local notation "X" => A.simpleFiniteModule q

def simpleNativeBarIso : (simpleOrdinaryResolution q).complex ≅
    ExternalTensor.complex k T₀ T₀ (ModuleBar.complex k T₀ S) (ModuleBar.complex k T₀ S) :=
  simpleOrdinaryBarIso q ≪≫ simpleCoefficientComplexIso q ≪≫
    ExternalBalanced.nativeTotalBarIso k T₀ T₀ S S

private theorem three_isos_hom_f {Cat : Type*} [Category Cat] [Limits.HasZeroMorphisms Cat]
    {source middle₁ middle₂ target : ChainComplex Cat ℕ}
    (firstIso : source ≅ middle₁) (secondIso : middle₁ ≅ middle₂)
    (thirdIso : middle₂ ≅ target) (degree : ℕ) :
    (firstIso ≪≫ secondIso ≪≫ thirdIso).hom.f degree =
      firstIso.hom.f degree ≫ (secondIso.hom.f degree ≫ thirdIso.hom.f degree) := rfl

private theorem simpleNativeBarIso_hom :
    (simpleNativeBarIso q).hom =
      (simpleOrdinaryBarIso q).hom ≫
        (simpleCoefficientComplexIso q ≪≫
          ExternalBalanced.nativeTotalBarIso k T₀ T₀ S S).hom := rfl

private theorem simpleCoefficientNativeIso_hom :
    (simpleCoefficientComplexIso q ≪≫
      ExternalBalanced.nativeTotalBarIso k T₀ T₀ S S).hom =
    (simpleCoefficientComplexIso q).hom ≫
      (ExternalBalanced.nativeTotalBarIso k T₀ T₀ S S).hom := rfl

/-- The degreewise map of the native comparison is the composite of its three factors. -/
theorem simpleNativeBarIso_hom_f (n : ℕ) :
    (simpleNativeBarIso q).hom.f n =
      (simpleOrdinaryBarIso q).hom.f n ≫
        ((simpleCoefficientComplexIso q).hom.f n ≫
          (ExternalBalanced.nativeTotalBarIso k T₀ T₀ S S).hom.f n) := by
  rw [simpleNativeBarIso_hom, simpleCoefficientNativeIso_hom,
    HomologicalComplex.comp_f]
  erw [HomologicalComplex.comp_f]

def simpleNativeFirst (n : ℕ) :=
  ModuleCat.ofHom (ExternalTensor.firstCubic k T₀ T₀
    (ModuleBar.complex k T₀ S) (ModuleBar.complex k T₀ S)
    (ModuleBar.cubicMap k T₀ S (CocycleData.p q)) n)

def simpleNativeSecond (n : ℕ) :=
  ModuleCat.ofHom (ExternalTensor.secondCubic k T₀ T₀
    (ModuleBar.complex k T₀ S) (ModuleBar.complex k T₀ S)
    (ModuleBar.cubicMap k T₀ S (CocycleData.p q)) n)

private theorem compose_native_squares {Cat : Type*} [Category Cat]
    {source middle target source' middle' target' : Cat}
    {sourceMap : source ⟶ source'} {middleMap : middle ⟶ middle'}
    {targetMap : target ⟶ target'} {first : source ⟶ middle}
    {first' : source' ⟶ middle'} {second : middle ⟶ target}
    {second' : middle' ⟶ target'}
    (firstSquare : sourceMap ≫ first' = first ≫ middleMap)
    (secondSquare : middleMap ≫ second' = second ≫ targetMap) :
    sourceMap ≫ (first' ≫ second') = (first ≫ second) ≫ targetMap := by
  rw [← Category.assoc, firstSquare, Category.assoc, secondSquare, ← Category.assoc]

private theorem simpleCoefficientNative_first (n : ℕ) :
    (EnvelopingBimodule.evaluationFunctor k A₀ (X).carrier).map (ordinaryFirstHom q n) ≫
      ((simpleCoefficientComplexIso q).hom.f n ≫
        (ExternalBalanced.nativeTotalBarIso k T₀ T₀ S S).hom.f n) =
    ((simpleCoefficientComplexIso q).hom.f (n+3) ≫
      (ExternalBalanced.nativeTotalBarIso k T₀ T₀ S S).hom.f (n+3)) ≫
        simpleNativeFirst q n := by
  exact compose_native_squares
    (simpleCoefficientComplexIso_comparison q (n+3) n (ordinaryFirstHom q n))
    (ExternalBalanced.nativeTotalBarIso_first k T₀ T₀ S S (CocycleData.p q) n)

private theorem simpleCoefficientNative_second (n : ℕ) :
    (EnvelopingBimodule.evaluationFunctor k A₀ (X).carrier).map (ordinarySecondHom q n) ≫
      ((simpleCoefficientComplexIso q).hom.f n ≫
        (ExternalBalanced.nativeTotalBarIso k T₀ T₀ S S).hom.f n) =
    ((simpleCoefficientComplexIso q).hom.f (n+3) ≫
      (ExternalBalanced.nativeTotalBarIso k T₀ T₀ S S).hom.f (n+3)) ≫
        simpleNativeSecond q n := by
  exact compose_native_squares
    (simpleCoefficientComplexIso_comparison q (n+3) n (ordinarySecondHom q n))
    (ExternalBalanced.nativeTotalBarIso_second k T₀ T₀ S S (CocycleData.p q) n)

theorem simpleNativeBarIso_first (n : ℕ) :
    ModuleCat.ofHom (TwoCone.evaluatedFirstBaseMap D hf X n) ≫
      (simpleNativeBarIso q).hom.f n =
    (simpleNativeBarIso q).hom.f (n+3) ≫ simpleNativeFirst q n := by
  rw [simpleNativeBarIso_hom_f, simpleNativeBarIso_hom_f]
  exact compose_native_squares (simpleOrdinaryBarIso_first q n)
    (simpleCoefficientNative_first q n)

theorem simpleNativeBarIso_second (n : ℕ) :
    ModuleCat.ofHom (TwoCone.evaluatedSecondBaseMap D hf X n) ≫
      (simpleNativeBarIso q).hom.f n =
    (simpleNativeBarIso q).hom.f (n+3) ≫ simpleNativeSecond q n := by
  rw [simpleNativeBarIso_hom_f, simpleNativeBarIso_hom_f]
  exact compose_native_squares (simpleOrdinaryBarIso_second q n)
    (simpleCoefficientNative_second q n)

end ArExplicit.T

end

end OAI
