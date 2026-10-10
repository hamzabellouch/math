import OAI.Probability.SignedSweeps.EvenWordCommutant

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {I J : Type*} [Fintype I] [Fintype J]

def euclideanEmbeddingLinear (e : I ↪ J) : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ J where
  toFun v := ∑ i, v i • EuclideanSpace.single (e i) 1
  map_add' v w := by simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

omit [Fintype J] in
lemma euclideanEmbeddingLinear_apply (e : I ↪ J) (v : EuclideanSpace ℂ I) (j : J) :
    euclideanEmbeddingLinear e v j = ∑ i, if e i = j then v i else 0 := by
  simp only [euclideanEmbeddingLinear, LinearMap.coe_mk, AddHom.coe_mk,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
  change (∑ i, v i * (if j = e i then 1 else 0)) = _
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : e i = j
  · simp only [h, ite_true, mul_one]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), mul_zero]

omit [Fintype J] in
lemma euclideanEmbeddingLinear_at (e : I ↪ J) (v : EuclideanSpace ℂ I) (i : I) :
    euclideanEmbeddingLinear e v (e i) = v i := by
  rw [euclideanEmbeddingLinear_apply]
  simp only [e.injective.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

omit [Fintype J] in
lemma euclideanEmbeddingLinear_off (e : I ↪ J) (v : EuclideanSpace ℂ I)
    {j : J} (hj : j ∉ Set.range e) : euclideanEmbeddingLinear e v j = 0 := by
  rw [euclideanEmbeddingLinear_apply]
  apply Finset.sum_eq_zero
  intro i _
  exact ite_eq_right (fun h => hj ⟨i, h⟩)

lemma euclideanEmbeddingLinear_inner (e : I ↪ J) (v w : EuclideanSpace ℂ I) :
    inner ℂ (euclideanEmbeddingLinear e v) (euclideanEmbeddingLinear e w) = inner ℂ v w := by
  change inner ℂ (∑ i, v i • EuclideanSpace.single (e i) 1) (euclideanEmbeddingLinear e w) = _
  rw [sum_inner]
  simp only [inner_smul_left, EuclideanSpace.inner_single_left, map_one, one_mul,
    euclideanEmbeddingLinear_at]
  simp only [PiLp.inner_apply, RCLike.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

def euclideanEmbedding (e : I ↪ J) : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ J :=
  (euclideanEmbeddingLinear e).isometryOfInner (euclideanEmbeddingLinear_inner e)

@[simp] lemma euclideanEmbedding_apply (e : I ↪ J) (v : EuclideanSpace ℂ I) :
    euclideanEmbedding e v = euclideanEmbeddingLinear e v := rfl

lemma euclideanEmbedding_single (e : I ↪ J) (i : I) :
    euclideanEmbedding e (EuclideanSpace.single i 1) = EuclideanSpace.single (e i) 1 := by
  ext j
  rw [euclideanEmbedding_apply, euclideanEmbeddingLinear_apply]
  simp only [PiLp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp [eq_comm]
  · intro k _ hki
    simp [hki]
  · simp

def euclideanTensorEquiv :
    (EuclideanSpace ℂ I ⊗[ℂ] EuclideanSpace ℂ J) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (I × J) :=
  ((EuclideanSpace.basisFun I ℂ).tensorProduct (EuclideanSpace.basisFun J ℂ)).repr

@[simp] lemma euclideanTensorEquiv_tmul (x : EuclideanSpace ℂ I) (y : EuclideanSpace ℂ J)
    (i : I) (j : J) : euclideanTensorEquiv (x ⊗ₜ[ℂ] y) (i,j) = x i * y j := by
  rw [euclideanTensorEquiv, OrthonormalBasis.tensorProduct_repr_tmul_apply]
  simp [mul_comm]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

def pairColorWord {u v p : ℕ} {C : Type*} (e : (Fin u ⊕ Fin v) ≃ Fin p)
    (w : (Fin u → C) × (Fin v → C)) : Fin p → C ⊕ C :=
  Sum.elim (fun i => Sum.inl (w.1 i)) (fun j => Sum.inr (w.2 j)) ∘ e.symm

def pairColorEmbedding {u v p : ℕ} {C : Type*} (e : (Fin u ⊕ Fin v) ≃ Fin p) :
    ((Fin u → C) × (Fin v → C)) ↪ (Fin p → C ⊕ C) where
  toFun := pairColorWord e
  inj' := by
    intro x y he
    apply Prod.ext
    · funext i
      have hi := congrFun he (e (Sum.inl i))
      simpa only [pairColorWord, Function.comp_apply, Equiv.symm_apply_apply,
        Sum.elim_inl, Sum.inl.injEq] using hi
    · funext j
      have hj := congrFun he (e (Sum.inr j))
      simpa only [pairColorWord, Function.comp_apply, Equiv.symm_apply_apply,
        Sum.elim_inr, Sum.inr.injEq] using hj

def pairWordEmbedding {u v p : ℕ} {C : Type*} [Fintype C]
    (e : (Fin u ⊕ Fin v) ≃ Fin p) :
    (WordSpace u C ⊗[ℂ] WordSpace v C) →ₗᵢ[ℂ] WordSpace p (C ⊕ C) :=
  (euclideanEmbedding (pairColorEmbedding e)).comp euclideanTensorEquiv.toLinearIsometry

lemma pairWordEmbedding_tmul_at {u v p : ℕ} {C : Type*} [Fintype C]
    (e : (Fin u ⊕ Fin v) ≃ Fin p) (x : WordSpace u C) (y : WordSpace v C)
    (w : Fin u → C) (z : Fin v → C) :
    pairWordEmbedding e (x ⊗ₜ[ℂ] y) (pairColorWord e (w,z)) = x w * y z := by
  change euclideanEmbeddingLinear (pairColorEmbedding e)
    (euclideanTensorEquiv (x ⊗ₜ[ℂ] y)) (pairColorEmbedding e (w,z)) = _
  rw [euclideanEmbeddingLinear_at, euclideanTensorEquiv_tmul]

end SignedSweeps
end

end OAI
