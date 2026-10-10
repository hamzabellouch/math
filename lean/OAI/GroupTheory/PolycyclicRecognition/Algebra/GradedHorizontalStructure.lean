import OAI.GroupTheory.PolycyclicRecognition.Algebra.GradedGeneratorLimit
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CoordinateConjugation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.WordChartHeight

namespace OAI

/-! # The horizontal projection and conjugation law of the graded limit -/

noncomputable section
namespace PolycyclicRecognition

open Module Filter
open scoped Topology BigOperators

/-- The degree-one part of exponential coordinates is linear in the
original horizontal vector. -/
def gradedGeneratorLinearMap
    {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}
    (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ) (s : ℝ) :
    L →ₗ[ℝ] (Fin n → ℝ) where
  toFun := gradedGenerator b cost s
  map_add' := by
    intro x y
    ext j
    by_cases hj : s = cost j <;> simp [gradedGenerator, hj]
  map_smul' := by
    intro c x
    ext j
    by_cases hj : s = cost j <;> simp [gradedGenerator, hj]

def gradedGeneratorMap
    {L : Type*} [LieRing L] [LieAlgebra ℝ L] [TopologicalSpace L]
    [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L] [FiniteDimensional ℝ L] {n : ℕ}
    (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ) (s : ℝ) :
    L →L[ℝ] (Fin n → ℝ) :=
  (gradedGeneratorLinearMap b cost s).toContinuousLinearMap

@[simp] theorem gradedGeneratorMap_apply
    {L : Type*} [LieRing L] [LieAlgebra ℝ L] [TopologicalSpace L]
    [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L] [FiniteDimensional ℝ L] {n : ℕ}
    (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ) (s : ℝ) (v : L) :
    gradedGeneratorMap b cost s v = gradedGenerator b cost s v := rfl

/-- A height that vanishes on brackets is unchanged by the horizontal
projection in a basis made of unit-cost words. -/
theorem gradedGenerator_word_height
    {L W I : Type*} [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup W] [Module ℝ W] [Fintype I] [DecidableEq I]
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (h : L →ₗ[ℝ] W) (hh : ∀ x y : L, h ⁅x, y⁆ = 0) (v : L) :
    let b := WordBasisSelections.basis X S β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    h (b.equivFun.symm (gradedGenerator b cost 1 v)) = h v := by
  dsimp only
  let b := WordBasisSelections.basis X S β
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
  have hhigh (j : Fin (finrank ℝ L)) (hj : (1 : ℝ) ≠ cost j) : h (b j) = 0 := by
    rw [← WordBasisSelections.eval_words X S β j]
    change h (evalBracketWord X (β.val j)) = 0
    cases hw : (β.val j : FreeMagma I) with
    | of i => exact (hj (by simp [cost, hw])).elim
    | mul u w => exact hh _ _
  conv_rhs => rw [← b.equivFun.symm_apply_apply v]
  rw [Basis.equivFun_symm_apply, Basis.equivFun_symm_apply, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_smul]
  change (if (1 : ℝ) = cost j then b.repr v j else 0) • h (b j) = b.repr v j • h (b j)
  by_cases hj : (1 : ℝ) = cost j
  · rw [ite_eq_left hj]
  · rw [ite_eq_right hj, hhigh j hj, smul_zero, smul_zero]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The actual representation-derived conjugation identity is closed under
the graded rescaling. -/
theorem graded_exponentialConjugationLaw
    {L G A : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    [Group G] [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    {n c : ℕ} (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (Exp x) = algebraExpUnit (j x)) :
    ExponentialConjugationLaw (dynkinProduct a (gradedCoordinateBracket b cost))
      (gradedCoordinateBracket b cost) := by
  exact (isClosed_exponentialConjugationLaw a).mem_of_tendsto
    (basisBracket_rescale_tendsto b cost hweight)
    (Eventually.of_forall fun r => basis_exponentialConjugationLaw
      (exponentialRescaleBasis b cost r) Exp hinj hneg a hm j ρ hρ hmatch)

end PolycyclicRecognition

end

end OAI
