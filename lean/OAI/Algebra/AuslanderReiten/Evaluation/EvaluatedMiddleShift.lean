import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedBaseShift
import OAI.Algebra.AuslanderReiten.Resolutions.FiniteResolutionProduct
import OAI.Algebra.AuslanderReiten.Coordinates.MappedBiproductHom
import OAI.Algebra.AuslanderReiten.HomComplex.TensorFullHomZero
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomShiftedHomotopy

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R" => A k q
local notation "X" => A.simpleFiniteModule q
local notation "D" => bimoduleTwoConeData q
local notation "hf" => bimodule_term_finite_k q
local notation "τ" => AFrobeniusTrace k q
local notation "HC" => HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ)
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)
abbrev evaluatedSimpleObject := (Q).obj ((X).completeCochain τ)
local notation "SX" => evaluatedSimpleObject q

abbrev evaluatedSingletonModule (n : ℕ) := (X).evaluated (TwoCone.middleCokernelModule D hf n)

abbrev evaluatedSingletonResolution (n : ℕ) :=
  (Q).obj ((evaluatedSingletonModule q n).completeCochain τ)

def evaluatedSingletonPairEquiv (n : ℕ) : (evaluatedSingletonModule q n).carrier ≃ₗ[R]
    (FiniteLeftModule.pairModule (evaluatedBaseModule q (n+2))
      (evaluatedBaseModule q (n+2))).carrier :=
  FiniteLeftModule.evaluatedPairEquiv X (TwoCone.baseCokernelModule D hf (n+2))
    (TwoCone.baseCokernelModule D hf (n+2))

def evaluatedSingletonProductIso (n : ℕ) : evaluatedSingletonResolution q n ≅
    (evaluatedBaseResolution q (n+2) ⊞ evaluatedBaseResolution q (n+2)) :=
  (FiniteLeftModule.resolutionIso τ (evaluatedSingletonPairEquiv q n)).trans
    (FiniteLeftModule.resolutionPairIso τ (evaluatedBaseModule q (n+2))
      (evaluatedBaseModule q (n+2)))

def evaluatedSingletonFst (n : ℕ) : (evaluatedSingletonModule q n).carrier →ₗ[R]
    (evaluatedBaseModule q (n+2)).carrier :=
  (LinearMap.fst R _ _).comp (evaluatedSingletonPairEquiv q n).toLinearMap

def evaluatedSingletonSnd (n : ℕ) : (evaluatedSingletonModule q n).carrier →ₗ[R]
    (evaluatedBaseModule q (n+2)).carrier :=
  (LinearMap.snd R _ _).comp (evaluatedSingletonPairEquiv q n).toLinearMap

@[simp] theorem evaluatedSingletonProductIso_fst (n : ℕ) :
    (evaluatedSingletonProductIso q n).hom ≫ biprod.fst =
      (Q).map (FiniteLeftModule.resolutionMap τ (evaluatedSingletonFst q n)) := by
  simp only [evaluatedSingletonProductIso, Iso.trans_hom, Category.assoc,
    FiniteLeftModule.resolutionPairIso_hom_fst, FiniteLeftModule.resolutionIso_hom]
  exact (FiniteLeftModule.resolutionMap_comp τ _ _).symm

@[simp] theorem evaluatedSingletonProductIso_snd (n : ℕ) :
    (evaluatedSingletonProductIso q n).hom ≫ biprod.snd =
      (Q).map (FiniteLeftModule.resolutionMap τ (evaluatedSingletonSnd q n)) := by
  simp only [evaluatedSingletonProductIso, Iso.trans_hom, Category.assoc,
    FiniteLeftModule.resolutionPairIso_hom_snd, FiniteLeftModule.resolutionIso_hom]
  exact (FiniteLeftModule.resolutionMap_comp τ _ _).symm

def evaluatedBaseFullHomEquiv (n : ℕ) (a : ℤ) :
    (SX ⟶ (evaluatedBaseResolution q n)⟦a⟧) ≃ₗ[k]
      CohomologyClass (A.simpleComplete q) (A.simpleComplete q) (a-(n:ℤ)) :=
  (evaluatedBaseHomEquiv q n a).trans
    (fullHomShiftedHomotopyEquiv k (A.simpleComplete q) (A.simpleComplete q) (a-(n:ℤ))).symm

def evaluatedSingletonHomEquiv (n : ℕ) (a : ℤ) :
    (SX ⟶ (evaluatedSingletonResolution q n)⟦a⟧) ≃ₗ[k]
      ((SX ⟶ (evaluatedBaseResolution q (n+2))⟦a⟧) ×
       (SX ⟶ (evaluatedBaseResolution q (n+2))⟦a⟧)) :=
  (Linear.homCongr k (Iso.refl _) ((CategoryTheory.shiftFunctor HC a).mapIso
    (evaluatedSingletonProductIso q n))).trans
      (mappedBiproductHomEquiv k (CategoryTheory.shiftFunctor HC a) SX
        (evaluatedBaseResolution q (n+2)) (evaluatedBaseResolution q (n+2)))

def evaluatedSingletonFullHomEquiv (n : ℕ) (a : ℤ) :
    (SX ⟶ (evaluatedSingletonResolution q n)⟦a⟧) ≃ₗ[k]
      (CohomologyClass (A.simpleComplete q) (A.simpleComplete q) (a-((n+2:ℕ):ℤ)) ×
       CohomologyClass (A.simpleComplete q) (A.simpleComplete q) (a-((n+2:ℕ):ℤ))) :=
  (evaluatedSingletonHomEquiv q n a).trans
    ((evaluatedBaseFullHomEquiv q (n+2) a).prodCongr (evaluatedBaseFullHomEquiv q (n+2) a))

end ArExplicit.T

end

end OAI
