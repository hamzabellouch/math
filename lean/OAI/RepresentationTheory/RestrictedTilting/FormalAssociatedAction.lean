import OAI.RepresentationTheory.RestrictedTilting.FormalSectionAction
import OAI.RepresentationTheory.RestrictedTilting.AssociatedPlaneJet
import OAI.RepresentationTheory.RestrictedTilting.NumeratorAction
import OAI.RepresentationTheory.RestrictedTilting.CompletionCoefficients
import OAI.RepresentationTheory.RestrictedTilting.CompletedCoordinates

namespace OAI

namespace FiberFunctorProof
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct BigOperators Pointwise
universe u
variable (k : Type u) [Field k] [Infinite k]
variable (ι : Type u) [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (Multiplicative k) (ι → k))
variable (P : Matrix ι ι (Polynomial k))
variable (hP : ∀ t : k, polynomialMatrixEval P t = LinearMap.toMatrix' (ρ (Multiplicative.ofAdd t)))
variable (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d)
local notation "N" => associatedSectionsSubmodule k ι ρ
local notation "A" => MvPolynomial (Fin 2) k
local notation "I" => MvPolynomial.idealOfVars (Fin 2) k
local notation "σ" => associatedSectionsRepresentation k ι ρ
local notation "hσ" => associatedSections_planeCompatible k ι ρ
local notation "W" => associatedNumeratorLinear k ι ρ P hP d hd
variable [Module.Finite k ((associatedSectionsSubmodule k ι ρ) ⧸
  planeJetRelation (M := associatedSectionsSubmodule k ι ρ) k 1)]
local notation "T" => planeJetFD k σ hσ 1

noncomputable def formalAssociatedCoordinates
    (s : (j : ℕ) → T ⟶ planeJetFD k σ hσ (j+1))
    (hs : ∀ j, s (j+1) ≫ planeJetTransitionHom k σ hσ (j+1) = s j) (v : T) :
    ι → planeCompletion k := completedCoordinates I W (formalPlaneSection k σ hσ s hs v)

omit [Infinite k] in
lemma linePolynomial_cleared (p : Polynomial k) (t : k) (d : ℕ) :
    linePolynomial k (clearedPolynomial p (MvPolynomial.C t) ((MvPolynomial.X 0 : A)^2) d) =
      clearedLineAction k p t d := by
  rw [map_clearedPolynomial]
  simp [linePolynomial, clearedLineAction]

omit [Infinite k] in
lemma formalLineMap_cleared (p : Polynomial k) (t : k) (d : ℕ) :
    formalLineMap k (algebraMap A (planeCompletion k)
      (clearedPolynomial p (MvPolynomial.C t) ((MvPolynomial.X 0 : A)^2) d)) =
      clearedPolynomial p (algebraMap k (PowerSeries k) t) ((PowerSeries.X : PowerSeries k)^2) d := by
  change formalLineMap k ((IsScalarTower.toAlgHom k A (planeCompletion k)) _) = _
  rw [map_clearedPolynomial, map_clearedPolynomial]
  simp only [IsScalarTower.toAlgHom_apply, map_pow, formalLineMap_X]
  congr 1
  rw [MvPolynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply,
    AlgHom.commutes]

lemma formalAssociatedCoordinates_unipotent
    (s : (j : ℕ) → T ⟶ planeJetFD k σ hσ (j+1))
    (hs : ∀ j, s (j+1) ≫ planeJetTransitionHom k σ hσ (j+1) = s j)
    (t : k) (v : T) (i : ι) :
    (PowerSeries.X : PowerSeries k)^(2*d) * formalLineMap k
      (formalAssociatedCoordinates k ι ρ P hP d hd s hs ((planeJetFD k σ hσ 1).ρ (unipotent k t) v) i) =
      ∑ j, clearedPolynomial (P i j) (algebraMap k (PowerSeries k) t)
        ((PowerSeries.X : PowerSeries k)^2) d * formalLineMap k
          (formalAssociatedCoordinates k ι ρ P hP d hd s hs v j) := by
  let F : N →ₗ[A] A := (MvPolynomial.X 0 : A)^(2*d) • (LinearMap.proj i).comp W
  let G : N →ₗ[A] A := ∑ j, clearedPolynomial (P i j) (MvPolynomial.C t)
    ((MvPolynomial.X 0 : A)^2) d • (LinearMap.proj j).comp W
  have he : ∀ f : N, linePolynomial k (F (σ (unipotent k t) f)) = linePolynomial k (G f) := by
    intro f
    simpa only [F,G,LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.comp_apply,
      LinearMap.proj_apply,smul_eq_mul,map_mul,map_pow,map_sum,
      show linePolynomial k (MvPolynomial.X 0) = Polynomial.X from by simp [linePolynomial],
      linePolynomial_cleared] using associatedNumerator_line_unipotent k ι ρ P hP d hd t f i
  have h := formalPlaneSection_line_action k σ hσ s hs (unipotent k t) F G he v
  simp only [F,G,completion_map_smul, LinearMap.sum_apply, completion_self_smul, map_mul, map_sum,
    map_pow, formalLineMap_X, formalLineMap_cleared] at h
  simpa only [formalAssociatedCoordinates, completedCoordinates_apply] using h
end FiberFunctorProof

end OAI
