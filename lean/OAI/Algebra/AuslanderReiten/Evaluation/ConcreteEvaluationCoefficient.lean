import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteEvaluatedBase
import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingCoefficientComplex
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorScalar

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

abbrev canonicalTensorSimple := ExternalTensor.canonicalTensorObject k T₀ T₀ S S

local instance canonicalSimpleScalar : Module k (canonicalTensorSimple q) :=
  moduleCatBaseModule (k := k) (R := A₀) (canonicalTensorSimple q)
local instance canonicalSimpleTower : IsScalarTower k A₀ (canonicalTensorSimple q) :=
  moduleCatBaseTower (k := k) (R := A₀) (canonicalTensorSimple q)

def nativeToCanonicalSimple : (A.simpleFiniteModule q).carrier ≅ canonicalTensorSimple q :=
  (ExternalTensor.canonicalTensorIso k T₀ T₀ S S).symm

def simpleCoefficientComplexIso :
    ((EnvelopingBimodule.evaluationFunctor k A₀ (A.simpleFiniteModule q).carrier).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (shuffledBarComplex q) ≅
    ((EnvelopingBimodule.evaluationFunctor k A₀ (canonicalTensorSimple q)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (shuffledBarComplex q) :=
  EnvelopingBimodule.coefficientComplexIso k A₀ (nativeToCanonicalSimple q) (shuffledBarComplex q)

theorem simpleCoefficientComplexIso_comparison (m n : ℕ)
    (f : (shuffledBarComplex q).X m ⟶ (shuffledBarComplex q).X n) :
    (EnvelopingBimodule.evaluationFunctor k A₀ (A.simpleFiniteModule q).carrier).map f ≫
        (simpleCoefficientComplexIso q).hom.f n =
      (simpleCoefficientComplexIso q).hom.f m ≫
        (EnvelopingBimodule.evaluationFunctor k A₀ (canonicalTensorSimple q)).map f :=
  EnvelopingBimodule.coefficientComplexIso_comparison k A₀
    (nativeToCanonicalSimple q) (shuffledBarComplex q) m n f

end ArExplicit.T

end

end OAI
