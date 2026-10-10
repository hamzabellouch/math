import OAI.Probability.SignedSweeps.WordEmbedding

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

lemma isometric_adjoint_apply (j : E →ₗᵢ[ℂ] F) (x : E) :
    j.toLinearMap.adjoint (j x) = x := by
  apply ext_inner_left ℂ
  intro y
  rw [LinearMap.adjoint_inner_right]
  exact j.inner_map_map y x

lemma isometric_adjoint_comp (j : E →ₗᵢ[ℂ] F) :
    j.toLinearMap.adjoint ∘ₗ j.toLinearMap = LinearMap.id := by
  ext x
  exact isometric_adjoint_apply j x

def hilbertBlock (j : E →ₗᵢ[ℂ] F) : (E →ₗ[ℂ] E) →ₗ[ℂ] (F →ₗ[ℂ] F) where
  toFun A := j.toLinearMap ∘ₗ A ∘ₗ j.toLinearMap.adjoint
  map_add' A B := by ext x; simp
  map_smul' c A := by ext x; simp

@[simp] lemma hilbertBlock_apply (j : E →ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) (x : F) :
    hilbertBlock j A x = j (A (j.toLinearMap.adjoint x)) := rfl

lemma hilbertBlock_on (j : E →ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) (x : E) :
    hilbertBlock j A (j x) = j (A x) := by
  rw [hilbertBlock_apply, isometric_adjoint_apply]

lemma hilbertBlock_mul (j : E →ₗᵢ[ℂ] F) (A B : E →ₗ[ℂ] E) :
    hilbertBlock j (A * B) = hilbertBlock j A * hilbertBlock j B := by
  ext x
  simp only [Module.End.mul_apply, hilbertBlock_apply, isometric_adjoint_apply]

lemma hilbertBlock_adjoint (j : E →ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) :
    (hilbertBlock j A).adjoint = hilbertBlock j A.adjoint := by
  change (j.toLinearMap ∘ₗ A ∘ₗ j.toLinearMap.adjoint).adjoint = _
  simp only [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
  rfl

lemma hilbertBlock_positive (j : E →ₗᵢ[ℂ] F) {A : E →ₗ[ℂ] E} (hA : A.IsPositive) :
    (hilbertBlock j A).IsPositive := hA.conj_adjoint j.toLinearMap

lemma hilbertBlock_symmetric (j : E →ₗᵢ[ℂ] F) {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric) :
    (hilbertBlock j A).IsSymmetric := hA.conj_adjoint j.toLinearMap

lemma hilbertBlock_idempotent (j : E →ₗᵢ[ℂ] F) {A : E →ₗ[ℂ] E} (hA : A * A = A) :
    hilbertBlock j A * hilbertBlock j A = hilbertBlock j A := by
  rw [← hilbertBlock_mul, hA]

lemma hilbertBlock_trace (j : E →ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) :
    LinearMap.trace ℂ F (hilbertBlock j A) = LinearMap.trace ℂ E A := by
  change LinearMap.trace ℂ F (j.toLinearMap ∘ₗ (A ∘ₗ j.toLinearMap.adjoint)) = _
  rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, isometric_adjoint_comp,
    LinearMap.comp_id]

lemma hilbertBlock_orthogonal {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D]
    [FiniteDimensional ℂ D] (j : E →ₗᵢ[ℂ] F) (k : D →ₗᵢ[ℂ] F)
    (hjk : ∀ x y, inner ℂ (j x) (k y) = 0) (A : E →ₗ[ℂ] E) (B : D →ₗ[ℂ] D) :
    hilbertBlock j A * hilbertBlock k B = 0 := by
  have hz (y : D) : j.toLinearMap.adjoint (k y) = 0 := by
    apply ext_inner_left ℂ
    intro x
    rw [LinearMap.adjoint_inner_right, inner_zero_right]
    exact hjk x y
  ext x
  simp only [Module.End.mul_apply, hilbertBlock_apply, hz, map_zero, LinearMap.zero_apply]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {I J : Type*} [Fintype I] [Fintype J]

lemma euclideanEmbedding_adjoint (e : I ↪ J) (x : EuclideanSpace ℂ J) (i : I) :
    (euclideanEmbedding e).toLinearMap.adjoint x i = x (e i) := by
  have h := LinearMap.adjoint_inner_right (euclideanEmbedding e).toLinearMap
    (EuclideanSpace.single i 1) x
  change inner ℂ (EuclideanSpace.single i 1) ((euclideanEmbedding e).toLinearMap.adjoint x) =
    inner ℂ (euclideanEmbedding e (EuclideanSpace.single i 1)) x at h
  rw [EuclideanSpace.inner_single_left, euclideanEmbedding_single,
    EuclideanSpace.inner_single_left, map_one, one_mul] at h
  simpa only [map_one, one_mul] using h

lemma euclideanEmbedding_orthogonal {K : Type*} [Fintype K] (e : I ↪ J) (f : K ↪ J)
    (hef : Disjoint (Set.range e) (Set.range f)) (x : EuclideanSpace ℂ I)
    (y : EuclideanSpace ℂ K) : inner ℂ (euclideanEmbedding e x) (euclideanEmbedding f y) = 0 := by
  change inner ℂ ((euclideanEmbedding e).toLinearMap x) (euclideanEmbedding f y) = 0
  rw [← LinearMap.adjoint_inner_right (euclideanEmbedding e).toLinearMap]
  have hz : (euclideanEmbedding e).toLinearMap.adjoint (euclideanEmbedding f y) = 0 := by
    ext i
    rw [euclideanEmbedding_adjoint]
    exact euclideanEmbeddingLinear_off f y (Set.disjoint_left.mp hef (Set.mem_range_self i))
  rw [hz, inner_zero_right]

lemma euclideanTensorEquiv_single (i : I) (j : J) :
    euclideanTensorEquiv (EuclideanSpace.single i 1 ⊗ₜ[ℂ] EuclideanSpace.single j 1) =
      EuclideanSpace.single (i,j) 1 := by
  ext ⟨k,l⟩
  rw [euclideanTensorEquiv_tmul]
  simp only [PiLp.single_apply, Prod.mk.injEq]
  by_cases hk : k = i <;> by_cases hl : l = j <;> simp [hk, hl]

end SignedSweeps
end

end OAI
