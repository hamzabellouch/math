import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedOrdinaryFunctor
import OAI.Algebra.AuslanderReiten.Cones.ConcreteTwoConeEvaluation

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R" => T k q
local notation "A₀" => A k q
local notation "D" => bimoduleTwoConeData q
local notation "hf" => bimodule_term_finite_k q
local notation "X" => A.simpleFiniteModule q
private abbrev simpleEvaluationFunctor := EnvelopingBimodule.evaluationFunctor k (A k q) (A.simpleFiniteModule q).carrier
local notation "E" => simpleEvaluationFunctor q

abbrev simpleOrdinaryResolution :=
  TwoCone.evaluatedOrdinaryResolution D hf X (bimodule_exact q)
    (baseTail_right_projective q) (bimodule_term_projective q)

abbrev shuffledBarComplex :=
  ((ExternalTensor.envelopingFunctor k R R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (ExternalTensor.complex k (AbsoluteBar.Enveloping k R) (AbsoluteBar.Enveloping k R)
      (AbsoluteBar.complex k R) (AbsoluteBar.complex k R))

def ordinaryBarTermIso (n : ℕ) : (D).term n ≅ (shuffledBarComplex q).X n := Iso.refl _

theorem ordinaryBarTermIso_d (n : ℕ) :
    (ordinaryBarTermIso q (n+1)).hom ≫ (shuffledBarComplex q).d (n+1) n =
      ModuleCat.ofHom ((D).d n) ≫ (ordinaryBarTermIso q n).hom := by
  dsimp only [ordinaryBarTermIso, Iso.refl_hom]
  erw [Category.id_comp]

def simpleOrdinaryBarIso : (simpleOrdinaryResolution q).complex ≅
    ((E).mapHomologicalComplex (ComplexShape.down ℕ)).obj (shuffledBarComplex q) :=
  TwoCone.evaluatedOrdinaryFunctorIso D hf X (shuffledBarComplex q)
    (ordinaryBarTermIso q) (ordinaryBarTermIso_d q)

def ordinaryFirstHom (n : ℕ) : (D).term (n+3) ⟶ (D).term n :=
  ConcreteCategory.ofHom (C := ModuleCat (A₀ ⊗[k] A₀ᵐᵒᵖ)) ((D).first n)

def ordinarySecondHom (n : ℕ) : (D).term (n+3) ⟶ (D).term n :=
  ConcreteCategory.ofHom (C := ModuleCat (A₀ ⊗[k] A₀ᵐᵒᵖ)) ((D).second n)

theorem simpleOrdinaryBarIso_first (n : ℕ) :
    ModuleCat.ofHom (TwoCone.evaluatedFirstBaseMap D hf X n) ≫
      (simpleOrdinaryBarIso q).hom.f n =
    (simpleOrdinaryBarIso q).hom.f (n+3) ≫
      (E).map (ordinaryFirstHom q n) := by
  exact TwoCone.evaluatedOrdinaryFunctorIso_comparison D hf X (shuffledBarComplex q)
    (ordinaryBarTermIso q) (ordinaryBarTermIso_d q) (n+3) n
    (ordinaryFirstHom q n) (ordinaryFirstHom q n) (by
      dsimp only [ordinaryBarTermIso, Iso.refl_hom]
      erw [Category.id_comp, Category.comp_id])

theorem simpleOrdinaryBarIso_second (n : ℕ) :
    ModuleCat.ofHom (TwoCone.evaluatedSecondBaseMap D hf X n) ≫
      (simpleOrdinaryBarIso q).hom.f n =
    (simpleOrdinaryBarIso q).hom.f (n+3) ≫
      (E).map (ordinarySecondHom q n) := by
  exact TwoCone.evaluatedOrdinaryFunctorIso_comparison D hf X (shuffledBarComplex q)
    (ordinaryBarTermIso q) (ordinaryBarTermIso_d q) (n+3) n
    (ordinarySecondHom q n) (ordinarySecondHom q n) (by
      dsimp only [ordinaryBarTermIso, Iso.refl_hom]
      erw [Category.id_comp, Category.comp_id])

end ArExplicit.T

end

end OAI
