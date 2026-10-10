import OAI.Probability.SignedSweeps.PairWordTypes
import OAI.Probability.SignedSweeps.PairTwirlLift

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
local instance (priority := 2000) pairCovarianceWordDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) pairCovarianceSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

lemma wordTypeProjection_perm_commute {p : ℕ} (μ : Partition p) {C : Type*} [Fintype C]
    (g : SymmetricGroup p) :
    wordTypeProjection μ C * wordRepresentation p C g =
      wordRepresentation p C g * wordTypeProjection μ C := by
  apply submodule_projection_commute
  · exact fun x hx => (isotypicSubrepresentation (spechtRepresentation μ)
      (wordRepresentation p C)).apply_mem_toSubmodule g hx
  · rw [unitary_representation_adjoint _ (fun g x => wordRepresentation_norm g x)]
    exact fun x hx => (isotypicSubrepresentation (spechtRepresentation μ)
      (wordRepresentation p C)).apply_mem_toSubmodule g⁻¹ hx

lemma wordRepresentation_single {p : ℕ} {C : Type*} [Fintype C]
    (g : SymmetricGroup p) (w : Fin p → C) :
    wordRepresentation p C g (EuclideanSpace.single w 1) =
      EuclideanSpace.single (w ∘ (g⁻¹ : SymmetricGroup p)) 1 := by
  ext z
  simp only [wordRepresentation_apply, PiLp.single_apply]
  have he : z ∘ g = w ↔ z = w ∘ (g⁻¹ : SymmetricGroup p) := by
    constructor
    · intro h; funext i; simpa using congrFun h (g⁻¹ i)
    · rintro rfl; ext i; simp
  simp only [he]

lemma pairWordEmbedding_single {u v p : ℕ} {C : Type*} [Fintype C]
    (e : (Fin u ⊕ Fin v) ≃ Fin p) (w : Fin u → C) (z : Fin v → C) :
    pairWordEmbedding e (EuclideanSpace.single w 1 ⊗ₜ[ℂ] EuclideanSpace.single z 1) =
      EuclideanSpace.single (pairColorWord e (w,z)) 1 := by
  change euclideanEmbedding (pairColorEmbedding e)
    (euclideanTensorEquiv (EuclideanSpace.single w 1 ⊗ₜ[ℂ] EuclideanSpace.single z 1)) = _
  have he := euclideanTensorEquiv_single (I := Fin u → C) (J := Fin v → C) w z
  rw [he]
  convert euclideanEmbedding_single (pairColorEmbedding e) (w,z) using 1
  · congr 1
    ext j
    simp only [PiLp.single_apply]
    split_ifs <;> rfl
  · ext j
    simp only [PiLp.single_apply]
    rfl

lemma pairWordEmbedding_reindex {u v p : ℕ} {C : Type*} [Fintype C]
    (e : (Fin u ⊕ Fin v) ≃ Fin p) (g : SymmetricGroup p) :
    wordRepresentation p (C ⊕ C) g ∘ₗ (pairWordEmbedding (C := C) e).toLinearMap =
      (pairWordEmbedding (C := C) (e.trans g)).toLinearMap := by
  apply ((EuclideanSpace.basisFun (Fin u → C) ℂ).tensorProduct
    (EuclideanSpace.basisFun (Fin v → C) ℂ)).toBasis.ext
  rintro ⟨w,z⟩
  simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.tensorProduct_apply,
    EuclideanSpace.basisFun_apply, LinearMap.comp_apply]
  change wordRepresentation p (C ⊕ C) g
    (pairWordEmbedding e (EuclideanSpace.single w 1 ⊗ₜ[ℂ] EuclideanSpace.single z 1)) =
    pairWordEmbedding (e.trans g) (EuclideanSpace.single w 1 ⊗ₜ[ℂ] EuclideanSpace.single z 1)
  rw [pairWordEmbedding_single, wordRepresentation_single, pairWordEmbedding_single]
  rfl

lemma pairWordEmbedding_internal {u v p : ℕ} {C : Type*} [Fintype C]
    (e : (Fin u ⊕ Fin v) ≃ Fin p) (a : SymmetricGroup u) (b : SymmetricGroup v) :
    (pairWordEmbedding (C := C) ((a.sumCongr b).trans e)).toLinearMap =
      (pairWordEmbedding (C := C) e).toLinearMap ∘ₗ
        TensorProduct.map (wordRepresentation u C a) (wordRepresentation v C b) := by
  apply ((EuclideanSpace.basisFun (Fin u → C) ℂ).tensorProduct
    (EuclideanSpace.basisFun (Fin v → C) ℂ)).toBasis.ext
  rintro ⟨w,z⟩
  simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.tensorProduct_apply,
    EuclideanSpace.basisFun_apply, LinearMap.comp_apply]
  change pairWordEmbedding ((a.sumCongr b).trans e)
    (EuclideanSpace.single w 1 ⊗ₜ[ℂ] EuclideanSpace.single z 1) =
    pairWordEmbedding e (TensorProduct.map (wordRepresentation u C a) (wordRepresentation v C b)
      (EuclideanSpace.single w 1 ⊗ₜ[ℂ] EuclideanSpace.single z 1))
  rw [TensorProduct.map_tmul, wordRepresentation_single, wordRepresentation_single,
    pairWordEmbedding_single, pairWordEmbedding_single]
  congr 1
  funext i
  cases hi : e.symm i <;> simp [pairColorWord, hi]

lemma allocation_factorEquiv {u v p : ℕ} (h : u+v=p) (S : EvenAllocation u p)
    (f : (Fin u ⊕ Fin v) ≃ Fin p) (hf : ∀ i, f (Sum.inl i) ∈ S.1) :
    ∃ a : SymmetricGroup u, ∃ b : SymmetricGroup v,
      f = (a.sumCongr b).trans (allocationEquiv h S) := by
  let t : Equiv.Perm (Fin u ⊕ Fin v) := f.trans (allocationEquiv h S).symm
  have ht : Set.MapsTo t (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro _ ⟨i,rfl⟩
    cases he : t (Sum.inl i) with
    | inl k => exact ⟨k,rfl⟩
    | inr j =>
      have hj : f (Sum.inl i) = allocationEquiv h S (Sum.inr j) := by
        have hx := congrArg (allocationEquiv h S) he
        simpa [t] using hx
      exact False.elim (allocationEquiv_right_not_mem h S j (hj ▸ hf i))
  obtain ⟨⟨a,b⟩, hab⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl ht
  refine ⟨a,b,?_⟩
  apply Equiv.ext
  intro i
  have hi := congrArg (fun k : Equiv.Perm (Fin u ⊕ Fin v) => allocationEquiv h S (k i)) hab
  simpa [t] using hi.symm

lemma hilbertBlock_precomp {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (j k : E →ₗᵢ[ℂ] F) (U P : E →ₗ[ℂ] E)
    (hk : k.toLinearMap = j.toLinearMap ∘ₗ U) (hUU : U * U.adjoint = 1)
    (hUP : U * P = P * U) : hilbertBlock k P = hilbertBlock j P := by
  change k.toLinearMap ∘ₗ P ∘ₗ k.toLinearMap.adjoint = j.toLinearMap ∘ₗ P ∘ₗ j.toLinearMap.adjoint
  rw [hk, LinearMap.adjoint_comp]
  have he : U ∘ₗ P ∘ₗ U.adjoint = P := by
    change U * P * U.adjoint = P
    rw [hUP, mul_assoc, hUU, mul_one]
  calc
    _ = j.toLinearMap ∘ₗ (U ∘ₗ P ∘ₗ U.adjoint) ∘ₗ j.toLinearMap.adjoint := by
      simp only [LinearMap.comp_assoc]
    _ = _ := by rw [he]

lemma pairTypeBlock_allocation {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (α : Partition u) (β : Partition v) (S : EvenAllocation u p)
    (f : (Fin u ⊕ Fin v) ≃ Fin p) (hf : ∀ i, f (Sum.inl i) ∈ S.1) :
    hilbertBlock (pairWordEmbedding (C := C) f)
        (TensorProduct.map (wordTypeProjection α C) (wordTypeProjection β C)) =
      hilbertBlock (pairWordEmbedding (C := C) (allocationEquiv h S))
        (TensorProduct.map (wordTypeProjection α C) (wordTypeProjection β C)) := by
  obtain ⟨a,b,rfl⟩ := allocation_factorEquiv h S f hf
  apply hilbertBlock_precomp _ _
    (TensorProduct.map (wordRepresentation u C a) (wordRepresentation v C b)) _
    (pairWordEmbedding_internal _ a b)
  · have ha : (wordRepresentation u C a).adjoint = wordRepresentation u C a⁻¹ :=
      unitary_representation_adjoint _ (fun g x => wordRepresentation_norm g x) a
    have hb : (wordRepresentation v C b).adjoint = wordRepresentation v C b⁻¹ :=
      unitary_representation_adjoint _ (fun g x => wordRepresentation_norm g x) b
    rw [TensorProduct.adjoint_map, ha, hb, ← TensorProduct.map_mul,
      ← map_mul, ← map_mul, mul_inv_cancel, mul_inv_cancel, map_one, map_one,
      TensorProduct.map_one]

  · rw [← TensorProduct.map_mul, ← TensorProduct.map_mul,
      wordTypeProjection_perm_commute, wordTypeProjection_perm_commute]

end SignedSweeps
end

end OAI
