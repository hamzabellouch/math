import OAI.Algebra.AuslanderReiten.Cones.TwoConeEvaluatedBoundary
import OAI.Algebra.AuslanderReiten.Coordinates.TensorFiniteLift
import OAI.Algebra.AuslanderReiten.Algebras.TensorSimple

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated
open scoped TensorProduct
namespace ArExplicit
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)

namespace A

def simpleFiniteModule : FiniteLeftModule k (A k q) where
  carrier := Simple q
  scalar := inferInstance
  tower := inferInstance
  finite := inferInstance
end A

namespace T
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
local notation "A₀" => A k q
local notation "D" => bimoduleTwoConeData q

theorem baseTail_right_projective (n : ℕ) : Module.Projective A₀ᵐᵒᵖ
    (EnvelopingBimodule k A₀ (TwoCone.baseCokernelModule D (bimodule_term_finite_k q) n).carrier) := by
  let j := tensorRightInclusion k A₀ A₀ᵐᵒᵖ
  let : Module.Projective A₀ᵐᵒᵖ (TwoCone.BaseCokernel ((bimoduleTwoConeData q).restrict j) 0) :=
    Module.Projective.of_equiv (baseRightEquiv q).symm
  let : Module.Projective A₀ᵐᵒᵖ (TwoCone.BaseCokernel ((bimoduleTwoConeData q).restrict j) n) :=
    TwoCone.baseCokernel_projective ((bimoduleTwoConeData q).restrict j)
      (TwoCone.restricted_exact j D (bimodule_exact q)) (baseTerm_right_projective q) n
  let e := (EnvelopingBimodule.rightEquiv
    (TwoCone.baseCokernelModule D (bimodule_term_finite_k q) n).carrier).trans
      (TwoCone.baseCokernelRestrictionEquiv j D n)
  exact Module.Projective.of_equiv e.symm

def simpleSkeletonTriangle (n : ℕ) :=
  TwoCone.evaluatedSkeletonTriangle D (bimodule_term_finite_k q) (bimodule_exact q)
    (baseTail_right_projective q) (A.simpleFiniteModule q) (AFrobeniusTrace k q) n

def simpleTopTriangle (n : ℕ) :=
  TwoCone.evaluatedTopTriangle D (bimodule_term_finite_k q) (bimodule_exact q)
    (baseTail_right_projective q) (A.simpleFiniteModule q) (AFrobeniusTrace k q) n

theorem simpleSkeletonTriangle_distinguished (n : ℕ) : simpleSkeletonTriangle q n ∈
    distTriang
      (HomotopyCategory (ModuleCat.{u} A₀) (ComplexShape.up ℤ)) :=
  TwoCone.evaluatedSkeletonTriangle_distinguished D (bimodule_term_finite_k q) (bimodule_exact q)
    (baseTail_right_projective q) (A.simpleFiniteModule q) (AFrobeniusTrace k q) n

theorem simpleTopTriangle_distinguished (n : ℕ) : simpleTopTriangle q n ∈
    distTriang
      (HomotopyCategory (ModuleCat.{u} A₀) (ComplexShape.up ℤ)) :=
  TwoCone.evaluatedTopTriangle_distinguished D (bimodule_term_finite_k q) (bimodule_exact q)
    (baseTail_right_projective q) (A.simpleFiniteModule q) (AFrobeniusTrace k q) n

def simpleHomFiltration (n : ℕ) :=
  TwoCone.evaluatedHomFiltration D (bimodule_term_finite_k q) (bimodule_exact q)
    (baseTail_right_projective q) (A.simpleFiniteModule q) (AFrobeniusTrace k q)
    ((HomotopyCategory.quotient _ _).obj ((A.simpleFiniteModule q).completeCochain (AFrobeniusTrace k q))) n

end T
end ArExplicit

end

end OAI
