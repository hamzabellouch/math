import OAI.Probability.SignedSweeps.PairExtension
import OAI.Probability.SignedSweeps.MarkedSector

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G H E F : Type*} [Group G] [Group H]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]

def conjugateRestrictionHom (ρ : Representation ℂ G E) (τ : Representation ℂ H F)
    (i j : H →* G) (s : G) (hs : ∀ h, j h = s * i h * s⁻¹) :
    Representation.IntertwiningMap (ρ.comp i) τ →ₗ[ℂ]
      Representation.IntertwiningMap (ρ.comp j) τ where
  toFun f := (f.toLinearMap ∘ₗ ρ s⁻¹).intertwiningMap_of_isIntertwiningMap _ _ (by
    intro h x
    change f (ρ s⁻¹ (ρ (j h) x)) = τ h (f (ρ s⁻¹ x))
    rw [hs h]
    have he : ρ s⁻¹ * ρ (s * i h * s⁻¹) = ρ (i h) * ρ s⁻¹ := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    change f ((ρ s⁻¹ * ρ (s * i h * s⁻¹)) x) = _
    rw [he]
    exact Representation.IntertwiningMap.isIntertwining (ρ.comp i) τ f h (ρ s⁻¹ x))
  map_add' f k := by rfl
  map_smul' c f := by rfl

lemma conjugateRestrictionHom_injective (ρ : Representation ℂ G E) (τ : Representation ℂ H F)
    (i j : H →* G) (s : G) (hs : ∀ h, j h = s * i h * s⁻¹) :
    Function.Injective (conjugateRestrictionHom ρ τ i j s hs) := by
  intro f k he
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  have h := congrArg (fun t : Representation.IntertwiningMap (ρ.comp j) τ => t (ρ s x)) he
  change f ((ρ s⁻¹ * ρ s) x) = k ((ρ s⁻¹ * ρ s) x) at h
  simpa only [← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
    Representation.IntertwiningMap.toLinearMap_apply] using h

lemma conjugate_restriction_multiplicity_le [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (ρ : Representation ℂ G E) (τ : Representation ℂ H F)
    (i j : H →* G) (s : G) (hs : ∀ h, j h = s * i h * s⁻¹) :
    finrank ℂ (Representation.IntertwiningMap (ρ.comp i) τ) ≤
      finrank ℂ (Representation.IntertwiningMap (ρ.comp j) τ) :=
  LinearMap.finrank_le_finrank_of_injective (conjugateRestrictionHom_injective ρ τ i j s hs)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma signed_occurrence_restriction_multiplicity {u v l n : ℕ} (h : u+v+l=n)
    (a : Partition u) (b : Partition v) (c : Partition l) (lam : Partition n)
    (hocc : SignedOccurrence h a b c lam) :
    spechtDimension c ≤ finrank ℂ (Representation.IntertwiningMap (spinRestriction h lam)
      (outerTensorRepresentation (spechtRepresentation a) (spechtRepresentation b.transpose))) := by
  obtain ⟨f,hf,hint⟩ := hocc
  let τ := outerTensorRepresentation (spechtRepresentation a) (spechtRepresentation b.transpose)
  let σ := (spechtRepresentation lam).comp (blockEmbeddingHom h)
  let k : Representation.IntertwiningMap (outerTensorRepresentation τ (spechtRepresentation c)) σ :=
    f.intertwiningMap_of_isIntertwiningMap _ _ (by rintro ⟨⟨g,t⟩,s⟩ x; exact hint g t s x)
  have hk : k ≠ 0 := by
    intro he
    have hx := congrArg (fun j => j ((spechtGenerator a ⊗ₜ[ℂ] spechtGenerator b.transpose) ⊗ₜ[ℂ] spechtGenerator c)) he
    change f _ = 0 at hx
    exact complex_tmul_ne_zero
      (complex_tmul_ne_zero (spechtGenerator_ne_zero a) (spechtGenerator_ne_zero b.transpose))
      (spechtGenerator_ne_zero c) (hf (hx.trans (map_zero f).symm))
  let := specht_irreducible a
  let := specht_irreducible b.transpose
  let := specht_irreducible c
  let := outerTensorRepresentation_irreducible (spechtRepresentation a) (spechtRepresentation b.transpose)
    (spechtRepresentation_norm a) (spechtRepresentation_norm b.transpose)
  exact multiplicity_of_outerTensor_occurrence τ (spechtRepresentation c) σ
    (outerTensorRepresentation_norm _ _ (spechtRepresentation_norm a) (spechtRepresentation_norm b.transpose))
    (spechtRepresentation_norm c) (fun g x => spechtRepresentation_norm lam _ x) k hk

lemma signed_occurrence_marked_restriction_multiplicity {u v p l n : ℕ}
    (hu : u+v=p) (h : p+l=n) (hn : u+v+l=n)
    (a : Partition u) (b : Partition v) (c : Partition l) (lam : Partition n)
    (hocc : SignedOccurrence hn a b c lam) (z : MarkedAssignment l n) (S : EvenAllocation u p) :
    spechtDimension c ≤ finrank ℂ (Representation.IntertwiningMap
      ((spechtRepresentation lam).comp (markedPairEmbeddingHom hu h z S))
      (outerTensorRepresentation (spechtRepresentation a) (spechtRepresentation b.transpose))) := by
  apply (signed_occurrence_restriction_multiplicity hn a b c lam hocc).trans
  let i := (allocationEquiv hu S).toEmbedding.trans (markedInjection h z)
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair (blockSpinInjection hn) i
    (blockSpinInjection hn).injective i.injective
  apply conjugate_restriction_multiplicity_le (spechtRepresentation lam)
    (outerTensorRepresentation (spechtRepresentation a) (spechtRepresentation b.transpose))
    _ _ σ
  rintro ⟨g,t⟩
  change ((allocationEquiv hu S).permCongr (g.sumCongr t)).viaEmbedding (markedInjection h z) =
    σ * blockEmbedding hn g t 1 * σ⁻¹
  rw [← viaEmbedding_equiv, ← viaEmbedding_trans]
  rw [blockEmbedding_one_remainder]
  exact (viaEmbedding_conjugate (blockSpinInjection hn) i σ hσ (g.sumCongr t)).symm

theorem signed_occurrence_marked_multiplicity {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (hn : u+v+l=n)
    (a : Partition u) (b : Partition v) (c : Partition l) (lam : Partition n)
    (colorA : Fin (a.1.colLen 0) ↪ C) (colorB : Fin (b.1.colLen 0) ↪ C)
    (hocc : SignedOccurrence hn a b c lam) (z : MarkedAssignment l n) (S : EvenAllocation u p) :
    spechtDimension c ≤ finrank ℂ (Representation.IntertwiningMap (spechtRepresentation lam)
      (markedSectorRepresentation hu h a b C)) := by
  apply (signed_occurrence_marked_restriction_multiplicity hu h hn a b c lam hocc z S).trans
  obtain ⟨j,hj,hjoff⟩ := marked_sector_isometric_fiber hu h a b colorA colorB z S
  exact embedded_fiber_multiplicity_le _ (markedPairEmbeddingHom_injective hu h z S)
    (spechtRepresentation lam) _ (markedSectorRepresentation hu h a b C) j.toLinearMap j.toLinearMap.adjoint
    (isometric_adjoint_comp j) hj (isometric_fiber_adjoint_off _ _ j hjoff)

end SignedSweeps
end

end OAI
