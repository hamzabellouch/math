import OAI.Probability.SignedSweeps.EvenDensity
import OAI.Probability.SignedSweeps.WordGrouping
import OAI.Probability.SignedSweeps.PiTensorHull

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
local instance (priority := 2000) groupedDensityMatrixDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
variable {J C : Type*} [Fintype J] [Fintype C] {p : ℕ} {k : J → ℕ}

lemma groupedWordMatrix_hull {T : J → Type*}
    (e : (Σ j, Fin (k j)) ≃ Fin p)
    (R : ∀ j, T j → Matrix (Fin (k j) → C) (Fin (k j) → C) ℂ)
    (A : ∀ j, Matrix (Fin (k j) → C) (Fin (k j) → C) ℂ)
    (hA : ∀ j, A j ∈ closedConvexHull ℝ (Set.range (R j))) :
    groupedWordMatrix e A ∈ closedConvexHull ℝ
      (Set.range (fun t : ∀ j, T j => groupedWordMatrix e (fun j => R j (t j)))) := by
  let L : Matrix (∀ j, Fin (k j) → C) (∀ j, Fin (k j) → C) ℂ →ₗ[ℝ]
      Matrix (Fin p → C) (Fin p → C) ℂ :=
    { toFun := fun M => M.submatrix (groupWordEquiv e) (groupWordEquiv e)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change L (piTensorMatrix A) ∈ _
  have hc := piTensorMatrix_closed_hull (fun j => Set.range (R j)) A hA
  apply closedConvexHull_min (t := L ⁻¹' closedConvexHull ℝ
      (Set.range (fun t : ∀ j, T j => groupedWordMatrix e (fun j => R j (t j))))) _
    (convex_closedConvexHull.linear_preimage L)
    (isClosed_closedConvexHull.preimage L.continuous_of_finiteDimensional) hc
  rintro _ ⟨B,hB,rfl⟩
  choose t ht using hB
  apply subset_closedConvexHull
  refine ⟨t, ?_⟩
  change groupedWordMatrix e (fun j => R j (t j)) = groupedWordMatrix e B
  congr 1
  funext j
  exact ht j

lemma wordMatrix_toContinuous_hull {C : Type*} [Fintype C] {p : ℕ} {T : Type*}
    (R : T → Matrix (Fin p → C) (Fin p → C) ℂ)
    (M : Matrix (Fin p → C) (Fin p → C) ℂ)
    (hM : M ∈ closedConvexHull ℝ (Set.range R)) :
    M.toEuclideanLin.toContinuousLinearMap ∈ closedConvexHull ℝ
      (Set.range (fun t => (R t).toEuclideanLin.toContinuousLinearMap)) := by
  let L := (LinearMap.toContinuousLinearMap.toLinearMap.comp
    (wordMatrixEquiv p C).symm.toAlgEquiv.toLinearMap).restrictScalars ℝ
  exact closedConvexHull_min (t := L ⁻¹' _) 
    (by rintro _ ⟨t,rfl⟩; exact subset_closedConvexHull ⟨t,rfl⟩)
    (convex_closedConvexHull.linear_preimage L)
    (isClosed_closedConvexHull.preimage L.continuous_of_finiteDimensional) hM

lemma wordContinuous_toMatrix_hull {C : Type*} [Fintype C] {p : ℕ} {T : Type*}
    (R : T → WordSpace p C →ₗ[ℂ] WordSpace p C)
    (M : WordSpace p C →L[ℂ] WordSpace p C)
    (hM : M ∈ closedConvexHull ℝ (Set.range (fun t => (R t).toContinuousLinearMap))) :
    wordMatrixEquiv p C M.toLinearMap ∈ closedConvexHull ℝ
      (Set.range (fun t => wordMatrixEquiv p C (R t))) := by
  let L : (WordSpace p C →L[ℂ] WordSpace p C) →ₗ[ℝ]
      Matrix (Fin p → C) (Fin p → C) ℂ :=
    { toFun := fun M => wordMatrixEquiv p C M.toLinearMap
      map_add' := fun A B => by rw [ContinuousLinearMap.toLinearMap_add, map_add]
      map_smul' := fun a A => by
        change wordMatrixEquiv p C (a • A.toLinearMap) = a • wordMatrixEquiv p C A.toLinearMap
        rw [← Complex.coe_smul, map_smul, Complex.coe_smul] }
  exact closedConvexHull_min (t := L ⁻¹' _) 
    (by rintro _ ⟨t,rfl⟩; exact subset_closedConvexHull ⟨t,rfl⟩)
    (convex_closedConvexHull.linear_preimage L)
    (isClosed_closedConvexHull.preimage L.continuous_of_finiteDimensional) hM

lemma groupedWordMatrix_domination
    (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A Q : ∀ j, Matrix (Fin (k j) → C) (Fin (k j) → C) ℂ)
    (a : J → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hA : ∀ j, (A j).PosSemidef) (hQ : ∀ j, (Q j).PosSemidef)
    (hdom : ∀ j, ((a j : ℂ) • A j - Q j).PosSemidef) :
    (((∏ j, a j : ℝ) : ℂ) • groupedWordMatrix e A - groupedWordMatrix e Q).PosSemidef := by
  have hs (j) : ((a j : ℂ) • A j).PosSemidef :=
    (hA j).smul (Complex.zero_le_real.mpr (ha j))
  have hb := groupedWordMatrix_lower e _ _ hs hQ hdom
  rw [groupedWordMatrix_scale, ← Complex.ofReal_prod] at hb
  exact hb

lemma wordMatrix_scaled_sub_positive {C : Type*} [Fintype C] {p : ℕ}
    (M P : WordSpace p C →ₗ[ℂ] WordSpace p C) (a : ℂ)
    (h : (a • M - P).IsPositive) :
    (a • wordMatrixEquiv p C M - wordMatrixEquiv p C P).PosSemidef := by
  rw [← map_smul, ← map_sub]
  apply Matrix.isPositive_toEuclideanLin_iff.mp
  change (((wordMatrixEquiv p C).symm) ((wordMatrixEquiv p C) (a • M - P))).IsPositive
  rw [StarAlgEquiv.symm_apply_apply]
  exact h

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
local instance (priority := 2000) groupedDensityCostDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _

def pairCarrierCost {u v : ℕ} (C : Type*) [Fintype C]
    (α : Partition u) (β : Partition v) : ℝ :=
  Real.exp (signedEntropy α β) *
    ((u+1 : ℝ)^(Fintype.card C * Fintype.card C) *
      (v+1 : ℝ)^(Fintype.card C * Fintype.card C))

lemma pairCarrierCost_pos {u v : ℕ} (C : Type*) [Fintype C]
    (α : Partition u) (β : Partition v) : 0 < pairCarrierCost C α β := by
  unfold pairCarrierCost
  positivity

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
local instance (priority := 2000) groupedDensityProjectionDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
variable {J C : Type*} [Fintype J] [Fintype C] {p : ℕ} {k u v : J → ℕ}

def groupedPairTypeProjection (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (α : ∀ j, Partition (u j)) (β : ∀ j, Partition (v j)) :
    WordSpace p (C ⊕ C) →ₗ[ℂ] WordSpace p (C ⊕ C) :=
  groupedWordOperator e (fun j => pairTypeProjection (h j) (α j) (β j) C)

lemma groupedPairTypeProjection_positive (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (α : ∀ j, Partition (u j)) (β : ∀ j, Partition (v j)) :
    (groupedPairTypeProjection (C := C) e h α β).IsPositive :=
  groupedWordOperator_positive e _ (fun j => pairTypeProjection_positive (h j) (α j) (β j) C)

lemma groupedPairTypeProjection_idempotent (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (α : ∀ j, Partition (u j)) (β : ∀ j, Partition (v j)) :
    groupedPairTypeProjection (C := C) e h α β * groupedPairTypeProjection e h α β =
      groupedPairTypeProjection e h α β :=
  groupedWordOperator_idempotent e _ (fun j => pairTypeProjection_idempotent (h j) (α j) (β j) C)

def groupedEvenTensor (e : (Σ j, Fin (k j)) ≃ Fin p) (R : J → EvenColorDensity C) :
    WordSpace p (C ⊕ C) →ₗ[ℂ] WordSpace p (C ⊕ C) :=
  (varyingWordTensor (fun i => (R (e.symm i).1).matrix)).toEuclideanLin

lemma groupedEvenTensor_eq (e : (Σ j, Fin (k j)) ≃ Fin p) (R : J → EvenColorDensity C) :
    groupedEvenTensor e R = groupedWordOperator e (fun j => (R j).tensor (k j)) := by
  change (varyingWordTensor (fun i => (R (e.symm i).1).matrix)).toEuclideanLin = _
  rw [← groupedWordMatrix_tensor e (fun j => (R j).matrix), groupedWordMatrix_toEuclideanLin]
  rfl

lemma evenColorMatrix_positive (R : EvenColorDensity C) : R.matrix.PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨R.even_positive.isHermitian.fromBlocks (by simp) R.odd_positive.isHermitian, ?_⟩
  intro x
  change 0 ≤ star x ⬝ᵥ (Matrix.fromBlocks R.even 0 0 R.odd).mulVec x
  rw [Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, add_zero, zero_add, dotProduct, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  exact add_nonneg (R.even_positive.dotProduct_mulVec_nonneg (x ∘ Sum.inl))
    (R.odd_positive.dotProduct_mulVec_nonneg (x ∘ Sum.inr))

omit [Fintype J] in
lemma groupedEvenTensor_positive [Fintype J]
    (e : (Σ j, Fin (k j)) ≃ Fin p) (R : J → EvenColorDensity C) :
    (groupedEvenTensor e R).IsPositive := by
  apply Matrix.isPositive_toEuclideanLin_iff.mpr
  exact piTensorMatrix_positive (fun i => (R (e.symm i).1).matrix)
    (fun i => evenColorMatrix_positive (R (e.symm i).1))

theorem grouped_even_density_domination [Nonempty C]
    (e : (Σ j, Fin (k j)) ≃ Fin p)
    (h : ∀ j, u j+v j=k j) (α : ∀ j, Partition (u j)) (β : ∀ j, Partition (v j))
    (hα : ∀ j, (α j).1.colLen 0 ≤ Fintype.card C)
    (hβ : ∀ j, (β j).1.colLen 0 ≤ Fintype.card C) :
    ∃ M : WordSpace p (C ⊕ C) →L[ℂ] WordSpace p (C ⊕ C),
      M ∈ closedConvexHull ℝ (Set.range (fun R : J → EvenColorDensity C =>
        (groupedEvenTensor e R).toContinuousLinearMap)) ∧
      M.toLinearMap.IsPositive ∧
      ((((∏ j, pairCarrierCost C (α j) (β j)) : ℝ) : ℂ) • M.toLinearMap -
        groupedPairTypeProjection e h α β).IsPositive := by
  choose M hM hpos hdom using fun j =>
    exists_even_density_domination (h j) (α j) (β j) (hα j) (hβ j)
  let A := fun j => wordMatrixEquiv (k j) (C ⊕ C) (M j).toLinearMap
  have hA (j) : (A j).PosSemidef :=
    Matrix.isPositive_toEuclideanLin_iff.mp (by simpa [A] using hpos j)
  have hh (j) : A j ∈ closedConvexHull ℝ (Set.range
      (fun R : EvenColorDensity C => wordTensorMatrix (k j) R.matrix)) := by
    have hm := wordContinuous_toMatrix_hull (fun R : EvenColorDensity C => R.tensor (k j)) (M j) (hM j)
    simpa only [EvenColorDensity.tensor, StarAlgEquiv.apply_symm_apply] using hm
  have hg := groupedWordMatrix_hull e (fun j (R : EvenColorDensity C) => wordTensorMatrix (k j) R.matrix) A hh
  have hg' := wordMatrix_toContinuous_hull
    (fun R : J → EvenColorDensity C => groupedWordMatrix e (fun j => wordTensorMatrix (k j) (R j).matrix))
    (groupedWordMatrix e A) hg
  refine ⟨(groupedWordMatrix e A).toEuclideanLin.toContinuousLinearMap, ?_,
    Matrix.isPositive_toEuclideanLin_iff.mpr (groupedWordMatrix_positive e A hA), ?_⟩
  · simpa only [groupedWordMatrix_tensor, groupedEvenTensor] using hg'
  · have hd (j) :
        ((pairCarrierCost C (α j) (β j) : ℂ) • A j -
          wordMatrixEquiv (k j) (C ⊕ C) (pairTypeProjection (h j) (α j) (β j) C)).PosSemidef :=
        wordMatrix_scaled_sub_positive _ _ _ (hdom j)
    have hq (j) : (wordMatrixEquiv (k j) (C ⊕ C)
        (pairTypeProjection (h j) (α j) (β j) C)).PosSemidef :=
      Matrix.isPositive_toEuclideanLin_iff.mp (by simpa using pairTypeProjection_positive (h j) (α j) (β j) C)
    have hb := groupedWordMatrix_domination e A _ _
      (fun j => (pairCarrierCost_pos C (α j) (β j)).le) hA hq hd
    have hp := Matrix.isPositive_toEuclideanLin_iff.mpr hb
    change (((wordMatrixEquiv p (C ⊕ C)).symm) (_ - _)).IsPositive at hp
    rw [map_sub, map_smul] at hp
    exact hp

end SignedSweeps
end

end OAI
