import OAI.Probability.SignedSweeps.PairCovariance

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
local instance (priority := 2000) pairCentralAllocationFunctionDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) pairCentralAllocationSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

def allocationMap {u p : ℕ} (g : SymmetricGroup p) : EvenAllocation u p ≃ EvenAllocation u p where
  toFun S := ⟨S.1.map g.toEmbedding, by simpa using S.2⟩
  invFun S := ⟨S.1.map g.symm.toEmbedding, by simpa using S.2⟩
  left_inv S := by
    apply Subtype.ext
    ext i
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, Equiv.symm_apply_apply]
  right_inv S := by
    apply Subtype.ext
    ext i
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, Equiv.apply_symm_apply]

lemma allocationMap_mem {u p : ℕ} (g : SymmetricGroup p) (S : EvenAllocation u p)
    {i : Fin p} (hi : i ∈ S.1) : g i ∈ (allocationMap g S).1 := by
  change g i ∈ S.1.map g.toEmbedding
  exact Finset.mem_map.mpr ⟨i,hi,rfl⟩

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
local instance (priority := 2000) pairCentralHilbertFunctionDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) pairCentralHilbertSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

lemma hilbertBlock_postcomp (j k : E →ₗᵢ[ℂ] F) (U : F →ₗ[ℂ] F) (P : E →ₗ[ℂ] E)
    (hk : k.toLinearMap = U ∘ₗ j.toLinearMap) :
    U * hilbertBlock j P * U.adjoint = hilbertBlock k P := by
  change U ∘ₗ (j.toLinearMap ∘ₗ P ∘ₗ j.toLinearMap.adjoint) ∘ₗ U.adjoint =
    k.toLinearMap ∘ₗ P ∘ₗ k.toLinearMap.adjoint
  rw [hk, LinearMap.adjoint_comp]
  simp only [LinearMap.comp_assoc]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
local instance (priority := 2000) pairCentralProjectionFunctionDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) pairCentralProjectionSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

lemma pairTypeProjection_permute_conj {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (α : Partition u) (β : Partition v) (g : SymmetricGroup p) :
    wordRepresentation p (C ⊕ C) g * pairTypeProjection h α β C *
        (wordRepresentation p (C ⊕ C) g).adjoint = pairTypeProjection h α β C := by
  let Q := TensorProduct.map (wordTypeProjection α C) (wordTypeProjection β C)
  unfold pairTypeProjection
  rw [Finset.mul_sum, Finset.sum_mul]
  calc
    _ = ∑ S : EvenAllocation u p,
        hilbertBlock (pairWordEmbedding (C := C) (allocationEquiv h (allocationMap g S))) Q := by
      apply Finset.sum_congr rfl
      intro S _
      rw [hilbertBlock_postcomp _ (pairWordEmbedding (C := C) ((allocationEquiv h S).trans g)) _ Q
        (pairWordEmbedding_reindex (allocationEquiv h S) g).symm]
      apply pairTypeBlock_allocation
      intro i
      exact allocationMap_mem g S (allocationEquiv_left_mem h S i)
    _ = _ := by
      simpa only [Q] using (allocationMap (u := u) g).sum_comp
        (fun S => hilbertBlock (pairWordEmbedding (C := C) (allocationEquiv h S)) Q)

theorem pairTypeProjection_perm_commute {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (α : Partition u) (β : Partition v) (g : SymmetricGroup p) :
    pairTypeProjection h α β C * wordRepresentation p (C ⊕ C) g =
      wordRepresentation p (C ⊕ C) g * pairTypeProjection h α β C := by
  have hg := pairTypeProjection_permute_conj (C := C) h α β g
  have hU : (wordRepresentation p (C ⊕ C) g).adjoint * wordRepresentation p (C ⊕ C) g = 1 := by
    rw [unitary_representation_adjoint _ (fun g x => wordRepresentation_norm g x),
      ← map_mul, inv_mul_cancel, map_one]
  have hh := congrArg (fun T => T * wordRepresentation p (C ⊕ C) g) hg
  rw [mul_assoc, mul_assoc, hU, mul_one] at hh
  exact hh.symm

lemma pairTypeProjection_mem_commutant {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (α : Partition u) (β : Partition v) :
    wordMatrixEquiv p (C ⊕ C) (pairTypeProjection h α β C) ∈ wordCommutant p (C ⊕ C) := by
  apply (wordMatrix_intertwining _).mp
  constructor
  intro g x
  exact LinearMap.congr_fun (pairTypeProjection_perm_commute h α β g) x

lemma pairWordEmbedding_off {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (S : EvenAllocation u p) (x : WordSpace u C ⊗[ℂ] WordSpace v C)
    (w : Fin p → C ⊕ C) (hw : wordEvenSites w ≠ S.1) :
    pairWordEmbedding (allocationEquiv h S) x w = 0 := by
  apply euclideanEmbeddingLinear_off
  exact fun he => hw ((pairColorEmbedding_range h S w).mp he)

lemma pairWordEmbedding_adjoint_off {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (S : EvenAllocation u p)
    (w : Fin p → C ⊕ C) (hw : wordEvenSites w ≠ S.1) :
    (pairWordEmbedding (C := C) (allocationEquiv h S)).toLinearMap.adjoint
      (EuclideanSpace.single w 1) = 0 := by
  apply ext_inner_left ℂ
  intro x
  rw [LinearMap.adjoint_inner_right, inner_zero_right, EuclideanSpace.inner_single_right]
  change 1 * starRingEnd ℂ (pairWordEmbedding (allocationEquiv h S) x w) = 0
  rw [pairWordEmbedding_off h S x w hw, map_zero, mul_zero]

lemma pairTypeProjection_parity_off {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (α : Partition u) (β : Partition v)
    (w z : Fin p → C ⊕ C) (hwz : wordEvenSites w ≠ wordEvenSites z) :
    wordMatrixEquiv p (C ⊕ C) (pairTypeProjection h α β C) w z = 0 := by
  simp only [wordMatrixEquiv, LinearMap.toMatrixOrthonormal_apply_apply,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, map_one, one_mul]
  unfold pairTypeProjection
  simp only [LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro S _
  rw [hilbertBlock_apply]
  by_cases hw : wordEvenSites w = S.1
  · have hz : wordEvenSites z ≠ S.1 := fun hz => hwz (hw.trans hz.symm)
    rw [pairWordEmbedding_adjoint_off h S z hz, map_zero, map_zero]
    rfl
  · exact pairWordEmbedding_off h S _ w hw

def colorParity {C : Type*} : C ⊕ C → Bool := Sum.elim (fun _ => false) (fun _ => true)

lemma colorParity_pattern_iff {p : ℕ} {C : Type*} (w z : Fin p → C ⊕ C) :
    colorParity ∘ w = colorParity ∘ z ↔ wordEvenSites w = wordEvenSites z := by
  constructor
  · intro hh
    ext i
    have hi := congrFun hh i
    cases hw : w i <;> cases hz : z i <;> simp [colorParity, hw, hz, mem_wordEvenSites] at hi ⊢
  · intro hh
    funext i
    have hi := Finset.ext_iff.mp hh i
    cases hw : w i <;> cases hz : z i <;> simp [colorParity, hw, hz, mem_wordEvenSites] at hi ⊢

theorem pairTypeProjection_even_span {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (α : Partition u) (β : Partition v) :
    wordMatrixEquiv p (C ⊕ C) (pairTypeProjection h α β C) ∈
      Submodule.span ℂ (Set.range (fun A : Matrix (C ⊕ C) (C ⊕ C) ℂ =>
        wordTensorMatrix p (colorClassCut colorParity A))) := by
  apply even_wordCommutant_span colorParity _ (pairTypeProjection_mem_commutant h α β)
  ext w z
  simp only [wordClassCut, colorClassCut_apply]
  split_ifs with hh
  · rfl
  · exact (pairTypeProjection_parity_off h α β w z
      (fun h => hh ((colorParity_pattern_iff w z).mpr h))).symm

end SignedSweeps
end

end OAI
