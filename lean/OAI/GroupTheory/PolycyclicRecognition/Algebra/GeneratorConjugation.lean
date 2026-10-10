import OAI.GroupTheory.PolycyclicRecognition.Algebra.GeneratorOrbit
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ConjugationFlow
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AlgebraExponential

namespace OAI

/-! # Actual group words realizing a basis of generator conjugates

A faithful exponential-compatible representation turns the operator words
from `GeneratorOrbit` into conjugation by finite words in generator
one-parameter subgroups. No generation or submersion assertion is assumed.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra

/-- A finite word using only the specified generator exponentials. -/
def generatorGroupWord {I L G : Type*} [SMul ℝ L] [Group G]
    (X : I → L) (Exp : L → G) (w : List (I × ℝ)) : G :=
  (w.map (fun p => Exp (p.2 • X p.1))).prod

@[simp] theorem generatorGroupWord_nil {I L G : Type*} [SMul ℝ L] [Group G]
    (X : I → L) (Exp : L → G) : generatorGroupWord X Exp [] = 1 := rfl

@[simp] theorem generatorGroupWord_cons {I L G : Type*} [SMul ℝ L] [Group G]
    (X : I → L) (Exp : L → G) (i : I) (t : ℝ) (w : List (I × ℝ)) :
    generatorGroupWord X Exp ((i, t) :: w) = Exp (t • X i) * generatorGroupWord X Exp w := rfl

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

local instance generatorConjugationNormedAddCommGroup : NormedAddCommGroup L :=
  NormedAddCommGroup.induced _ _ (finBasis ℝ L).equivFun.toLinearMap
    (finBasis ℝ L).equivFun.injective
local instance generatorConjugationNormedSpace : NormedSpace ℝ L :=
  NormedSpace.induced ℝ _ _ (finBasis ℝ L).equivFun.toLinearMap

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A Lie representation intertwines the full adjoint exponential with
ordinary algebra conjugation. -/
theorem represented_exp_continuousAd (j : L →ₗ⁅ℝ⁆ A) (x v : L) (t : ℝ) :
    j (NormedSpace.exp (t • continuousAd x) v) =
      NormedSpace.exp (t • j x) * j v * NormedSpace.exp (-(t • j x)) := by
  let f : L →L[ℝ] A := j.toLinearMap.toContinuousLinearMap
  have h := exp_intertwine_apply f (t • continuousAd x) (t • adjointOperator (j x))
    (by intro y; simp only [smul_apply, map_smul, continuousAd_apply,
      adjointOperator_apply]; exact congrArg (t • ·) (j.map_lie x y)) v
  rw [exp_smul_adjointOperator_apply] at h
  exact h

variable {G : Type*} [Group G] (X : I → L) (Exp : L → G)

variable (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
  (hExp : ∀ x, ρ (Exp x) = algebraExpUnit (j x))

include hρ hExp in
/-- Conjugation along one generator is the exponential of its actual adjoint. -/
theorem exp_ad_eq_group_conjugation (x v : L) (t : ℝ) :
    Exp (NormedSpace.exp (t • continuousAd x) v) =
      Exp (t • x) * Exp v * (Exp (t • x))⁻¹ := by
  apply hρ
  rw [map_mul, map_mul, map_inv, hExp, hExp, hExp, map_smul,
    represented_exp_continuousAd]
  exact algebraExpUnit_conj (algebraExpUnit (t • j x)) (j v)

include hρ hExp in
/-- The whole operator word is conjugation by its matching group word. -/
theorem exp_adjointWord_eq_group_conjugation (w : List (I × ℝ)) (v : L) :
    Exp (generatorAdjointWord X w v) =
      generatorGroupWord X Exp w * Exp v * (generatorGroupWord X Exp w)⁻¹ := by
  induction w with
  | nil => simp
  | cons p w ih =>
    rcases p with ⟨i, t⟩
    rw [generatorAdjointWord_cons, generatorGroupWord_cons]
    change Exp (NormedSpace.exp (t • continuousAd (X i)) (generatorAdjointWord X w v)) = _
    rw [exp_ad_eq_group_conjugation Exp j ρ hρ hExp, ih]
    group

include hρ hExp in
/-- Every finite-dimensional generated algebra has a basis of directions
whose full one-parameter subgroups are generator-word conjugates. -/
theorem exists_generatorGroupWord_basis
    (hX : LieSubalgebra.lieSpan ℝ L (Set.range X) = ⊤) :
    ∃ (b : Basis (Fin (finrank ℝ L)) ℝ L)
      (w : Fin (finrank ℝ L) → List (I × ℝ)) (i : Fin (finrank ℝ L) → I),
      ∀ k (t : ℝ), Exp (t • b k) =
        generatorGroupWord X Exp (w k) * Exp (t • X (i k)) *
          (generatorGroupWord X Exp (w k))⁻¹ := by
  obtain ⟨b, w, i, hb⟩ := exists_generatorOrbit_basis X hX
  refine ⟨b, w, i, ?_⟩
  intro k t
  rw [← hb k, ← map_smul]
  exact exp_adjointWord_eq_group_conjugation X Exp j ρ hρ hExp (w k) (t • X (i k))

end PolycyclicRecognition

end

end OAI
