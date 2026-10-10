import OAI.Probability.SignedSweeps.PairConstituents

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma viaEmbedding_equiv {A B : Type*} (e : A ≃ B) (g : Equiv.Perm A) :
    g.viaEmbedding e.toEmbedding = e.permCongr g := by
  apply Equiv.ext
  intro y
  obtain ⟨x,rfl⟩ := e.surjective y
  change (g.viaEmbedding e.toEmbedding) (e.toEmbedding x) = _
  rw [Equiv.Perm.viaEmbedding_apply]
  simp [Equiv.permCongr_apply]

theorem signed_occurrence_of_pair_injection {u v l n : ℕ} (h : u+v+l=n)
    (a : Partition u) (b : Partition v) (lam : Partition n)
    (i : (Fin u ⊕ Fin v) ↪ Fin n)
    (f : (Specht a ⊗[ℂ] Specht b.transpose) →ₗ[ℂ] Specht lam)
    (hf : Function.Injective f)
    (hint : ∀ (g : SymmetricGroup u) (t : SymmetricGroup v) x,
      f (TensorProduct.map (spechtRepresentation a g) (spechtRepresentation b.transpose t) x) =
        spechtRepresentation lam ((g.sumCongr t).viaEmbedding i) (f x)) :
    ∃ c : Partition l, SignedOccurrence h a b c lam := by
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair
    (blockSpinInjection h) i (blockSpinInjection h).injective i.injective
  have hconj (g : SymmetricGroup u) (t : SymmetricGroup v) :
      σ * blockEmbedding h g t 1 * σ⁻¹ = (g.sumCongr t).viaEmbedding i := by
    rw [blockEmbedding_one_remainder]
    exact viaEmbedding_conjugate _ _ σ hσ _
  let k := ((spechtRepresentation lam σ⁻¹) ∘ₗ f).intertwiningMap_of_isIntertwiningMap
    (outerTensorRepresentation (spechtRepresentation a) (spechtRepresentation b.transpose))
    (spinRestriction h lam) (by
      rintro ⟨g,t⟩ x
      change spechtRepresentation lam σ⁻¹ (f (TensorProduct.map (spechtRepresentation a g) (spechtRepresentation b.transpose t) x)) =
        spechtRepresentation lam (blockEmbedding h g t 1) (spechtRepresentation lam σ⁻¹ (f x))
      rw [hint]
      change (spechtRepresentation lam σ⁻¹ * spechtRepresentation lam ((g.sumCongr t).viaEmbedding i)) (f x) =
        (spechtRepresentation lam (blockEmbedding h g t 1) * spechtRepresentation lam σ⁻¹) (f x)
      rw [← map_mul, ← map_mul, ← hconj]
      simp only [← mul_assoc, inv_mul_cancel, one_mul])
  apply signed_occurrence_of_spin_intertwiner h a b lam k
  intro hz
  have he := congrArg (fun t => spechtRepresentation lam σ
    (t (spechtGenerator a ⊗ₜ[ℂ] spechtGenerator b.transpose))) hz
  change (spechtRepresentation lam σ * spechtRepresentation lam σ⁻¹)
    (f (spechtGenerator a ⊗ₜ[ℂ] spechtGenerator b.transpose)) = 0 at he
  rw [← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at he
  exact complex_tmul_ne_zero (spechtGenerator_ne_zero a) (spechtGenerator_ne_zero b.transpose)
    (hf (he.trans (map_zero f).symm))

theorem signed_occurrence_of_sector_extension {u v p l n : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (hn : u+v+l=n) (a : Partition u) (b : Partition v)
    (mu : Partition p) (lam : Partition n) (i : Fin p ↪ Fin n)
    (f : Representation.IntertwiningMap (spechtRepresentation mu) (signedWordRepresentation p C))
    (hf : f ≠ 0) (hQ : ∀ x, pairTypeProjection h a b C (f x) = f x)
    (F : Representation.IntertwiningMap (spechtRepresentation mu)
      ((spechtRepresentation lam).comp (Equiv.Perm.viaEmbeddingHom i))) (hF : F ≠ 0) :
    ∃ c : Partition l, SignedOccurrence hn a b c lam := by
  obtain ⟨S,k,hk,hint⟩ := pair_sector_constituent_occurrence h a b mu f hf hQ
  let e := allocationEquiv h S
  let := specht_irreducible mu
  have hFi : Function.Injective F :=
    (Representation.IsIrreducible.injective_or_eq_zero F).resolve_right hF
  apply signed_occurrence_of_pair_injection hn a b lam
    (e.toEmbedding.trans i) (F.toLinearMap ∘ₗ k) (hFi.comp hk)
  intro g t x
  change F (k (TensorProduct.map _ _ x)) = _
  rw [hint, F.isIntertwining]
  change spechtRepresentation lam ((e.permCongr (g.sumCongr t)).viaEmbedding i) (F (k x)) = _
  rw [viaEmbedding_trans, viaEmbedding_equiv]
  rfl

end SignedSweeps
end

end OAI
