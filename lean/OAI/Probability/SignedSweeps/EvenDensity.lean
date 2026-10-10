import OAI.Probability.SignedSweeps.PairDensityUpper
import OAI.Probability.SignedSweeps.PairEntropyDensity

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
local instance (priority := 2000) {C D : Type*} : DecidableEq (C ⊕ D) := Classical.decEq _

structure EvenColorDensity (C : Type*) [Fintype C] where
  even : Matrix C C ℂ
  odd : Matrix C C ℂ
  even_positive : even.PosSemidef
  odd_positive : odd.PosSemidef
  trace_one : even.trace.re + odd.trace.re = 1

end SignedSweeps
end

noncomputable section
namespace SignedSweeps.EvenColorDensity
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
local instance (priority := 2000) {C D : Type*} : DecidableEq (C ⊕ D) := Classical.decEq _
variable {C : Type*} [Fintype C]

def matrix (R : EvenColorDensity C) : Matrix (C ⊕ C) (C ⊕ C) ℂ :=
  Matrix.fromBlocks R.even 0 0 R.odd

def tensor (p : ℕ) (R : EvenColorDensity C) :
    WordSpace p (C ⊕ C) →ₗ[ℂ] WordSpace p (C ⊕ C) :=
  (wordMatrixEquiv p (C ⊕ C)).symm (wordTensorMatrix p R.matrix)

lemma tensor_commute {u v p : ℕ} (h : u+v=p) (α : Partition u) (β : Partition v)
    (R : EvenColorDensity C) :
    R.tensor p * pairTypeProjection h α β C = pairTypeProjection h α β C * R.tensor p :=
  pairTypeProjection_tensor_commute h α β R.even R.odd

lemma tensor_entropy_upper {u v p q : ℕ} (h : u+v=p) (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ q) (hβ : β.1.colLen 0 ≤ q) (R : EvenColorDensity (Fin q)) :
    ‖(R.tensor p * pairTypeProjection h α β (Fin q)).toContinuousLinearMap‖ ≤
      Real.exp (-signedEntropy α β) :=
  pair_density_opNorm_le h α β hα hβ R.even R.odd R.even_positive R.odd_positive R.trace_one.le

def conjugateDiagonal (x y : C → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hxy : (∑ i, x i) + (∑ i, y i) = 1)
    (U V : Matrix.unitaryGroup C ℂ) : EvenColorDensity C where
  even := U.1 * Matrix.diagonal (fun i => (x i : ℂ)) * star U.1
  odd := V.1 * Matrix.diagonal (fun i => (y i : ℂ)) * star V.1
  even_positive := (Matrix.posSemidef_diagonal_iff.mpr
    (fun i => Complex.zero_le_real.mpr (hx i))).mul_mul_conjTranspose_same U.1
  odd_positive := (Matrix.posSemidef_diagonal_iff.mpr
    (fun i => Complex.zero_le_real.mpr (hy i))).mul_mul_conjTranspose_same V.1
  trace_one := by
    rw [matrix_unitary_diagonal_trace_re x U _ rfl,
      matrix_unitary_diagonal_trace_re y V _ rfl, hxy]

end SignedSweeps.EvenColorDensity
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
local instance (priority := 2000) {C D : Type*} : DecidableEq (C ⊕ D) := Classical.decEq _

lemma pair_twirl_mem_density_hull {p : ℕ} {C : Type*} [Fintype C]
    (x y : C → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hxy : (∑ i, x i) + (∑ i, y i) = 1)
    {M : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ}
    (hM : matrixHilbertEquiv M ∈ pairTensorOrbitHull p
      (Matrix.diagonal (fun i => (x i : ℂ))) (Matrix.diagonal (fun i => (y i : ℂ)))) :
    ((wordMatrixEquiv p (C ⊕ C)).symm M).toContinuousLinearMap ∈
      closedConvexHull ℝ (Set.range (fun R : EvenColorDensity C => (R.tensor p).toContinuousLinearMap)) := by
  let L : MatrixHilbert (Fin p → C ⊕ C) →ₗ[ℝ]
      (WordSpace p (C ⊕ C) →L[ℂ] WordSpace p (C ⊕ C)) :=
    ((LinearMap.toContinuousLinearMap.toLinearMap.comp
      (wordMatrixEquiv p (C ⊕ C)).symm.toAlgEquiv.toLinearMap).comp
        matrixHilbertEquiv.symm.toLinearMap).restrictScalars ℝ
  have hm : matrixHilbertEquiv M ∈ closedConvexHull ℝ (Set.range
      (fun g => matrixConjugationAction (pairWordUnitaryHom p) g
        (matrixHilbertEquiv (wordTensorMatrix p (Matrix.fromBlocks
          (Matrix.diagonal (fun i => (x i : ℂ))) 0 0 (Matrix.diagonal (fun i => (y i : ℂ)))))))) := by
    simpa only [pairTensorOrbitHull, closedOrbitHull_eq_closedConvexHull] using hM
  apply linear_mem_closed_convex L isClosed_closedConvexHull convex_closedConvexHull _ hm
  rintro _ ⟨⟨U,V⟩,rfl⟩
  apply subset_closedConvexHull
  refine ⟨EvenColorDensity.conjugateDiagonal x y hx hy hxy U V, ?_⟩
  change ((wordMatrixEquiv p (C ⊕ C)).symm (wordTensorMatrix p _)).toContinuousLinearMap =
    ((wordMatrixEquiv p (C ⊕ C)).symm
      ((pairWordUnitaryHom p (U,V) : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ) *
        wordTensorMatrix p (Matrix.fromBlocks (Matrix.diagonal (fun i => (x i : ℂ))) 0 0
          (Matrix.diagonal (fun i => (y i : ℂ)))) *
        star (pairWordUnitaryHom p (U,V) : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ))).toContinuousLinearMap
  rw [pair_tensor_conjugate]
  rfl

theorem exists_even_density_domination {u v p : ℕ} {C : Type*} [Fintype C] [Nonempty C]
    (h : u+v=p) (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ Fintype.card C) (hβ : β.1.colLen 0 ≤ Fintype.card C) :
    ∃ M : WordSpace p (C ⊕ C) →L[ℂ] WordSpace p (C ⊕ C),
      M ∈ closedConvexHull ℝ (Set.range (fun R : EvenColorDensity C => (R.tensor p).toContinuousLinearMap)) ∧
      M.toLinearMap.IsPositive ∧
      ((((Real.exp (signedEntropy α β) *
          ((u+1 : ℝ)^(Fintype.card C * Fintype.card C) *
            (v+1 : ℝ)^(Fintype.card C * Fintype.card C))) : ℝ) : ℂ) • M.toLinearMap -
        pairTypeProjection h α β C).IsPositive := by
  obtain ⟨x,y,M,hx,hy,hxy,hM,hpos,hdom⟩ := exists_pair_entropy_density h α β hα hβ
  refine ⟨((wordMatrixEquiv p (C ⊕ C)).symm M).toContinuousLinearMap,
    pair_twirl_mem_density_hull x y hx hy hxy hM, ?_, hdom⟩
  exact Matrix.isPositive_toEuclideanLin_iff.mpr hpos

end SignedSweeps
end

end OAI
