import OAI.Probability.SignedSweeps.PairTwirlLift

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module

theorem subdiagram_specht_occurs_at {m n : ℕ} (μ : Partition m) (lam : Partition n)
    (h : μ.1 ≤ lam.1) (i : Fin m ↪ Fin n) :
    ∃ f : Representation.IntertwiningMap (spechtRepresentation μ)
      ((spechtRepresentation lam).comp (Equiv.Perm.viaEmbeddingHom i)), Function.Injective f := by
  obtain ⟨f, hf⟩ := subdiagram_specht_occurs μ lam h
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (subdiagramLabels h) i (subdiagramLabels h).injective i.injective
  have he (g : SymmetricGroup m) :
      g.viaEmbedding i * σ = σ * subdiagramEmbedding h g := by
    rw [← viaEmbedding_conjugate (subdiagramLabels h) i σ hσ g]
    simp only [mul_assoc, inv_mul_cancel, mul_one, subdiagramEmbedding,
      Equiv.Perm.viaEmbeddingHom_apply]
  let f' := ((spechtRepresentation lam σ).comp f.toLinearMap).intertwiningMap_of_isIntertwiningMap
    (spechtRepresentation μ)
    ((spechtRepresentation lam).comp (Equiv.Perm.viaEmbeddingHom i)) (by
      intro g x
      change spechtRepresentation lam σ (f (spechtRepresentation μ g x)) =
        spechtRepresentation lam (g.viaEmbedding i) (spechtRepresentation lam σ (f x))
      rw [f.isIntertwining]
      change (spechtRepresentation lam σ * spechtRepresentation lam (subdiagramEmbedding h g)) (f x) =
        (spechtRepresentation lam (g.viaEmbedding i) * spechtRepresentation lam σ) (f x)
      rw [← map_mul, ← map_mul, he])
  refine ⟨f', ?_⟩
  intro x y hxy
  apply hf
  have hσi := congrArg (spechtRepresentation lam σ⁻¹) hxy
  change (spechtRepresentation lam σ⁻¹ * spechtRepresentation lam σ) (f x) =
    (spechtRepresentation lam σ⁻¹ * spechtRepresentation lam σ) (f y) at hσi
  simpa only [← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] using hσi

lemma sum_spechtDimensions_le {m : ℕ} {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (SymmetricGroup m) E) (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (μ : I → Partition m) (hμ : Function.Injective μ)
    (hocc : ∀ i, ∃ f : Representation.IntertwiningMap (spechtRepresentation (μ i)) ρ,
      Function.Injective f) :
    ∑ i, spechtDimension (μ i) ≤ finrank ℂ E := by
  have hcopy (i : I) : ∃ j : Representation.IntertwiningMap (spechtRepresentation (μ i)) ρ,
      ∀ x, ‖j x‖ = ‖x‖ := by
    let := specht_irreducible (μ i)
    obtain ⟨j, hj⟩ := hocc i
    apply intertwiner_isometric_normalization _ _ (spechtRepresentation_norm (μ i)) hρ j
    intro hz
    exact spechtGenerator_ne_zero (μ i) (hj (by
      simp only [hz, Representation.IntertwiningMap.coe_zero, Pi.zero_apply]))
  choose j hj using hcopy
  let adj (i : I) := adjointIntertwiner (spechtRepresentation (μ i)) ρ
    (spechtRepresentation_norm (μ i)) hρ (j i)
  have hcross (a b : I) (hab : a ≠ b) (x : Specht (μ b)) : adj a (j b x) = 0 := by
    have hz := specht_hom_eq_zero_of_ne (μ b) (μ a) (hμ.ne hab.symm) ((adj a).comp (j b))
    exact congrArg (fun t => t x) hz
  have hdiag (a : I) (x : Specht (μ a)) : adj a (j a x) = x :=
    adjoint_isometric_intertwiner _ _ (j a) (hj a) x
  let L : (∀ i, Specht (μ i)) →ₗ[ℂ] E := {
    toFun v := ∑ i, j i (v i)
    map_add' := by intros; simp [Finset.sum_add_distrib]
    map_smul' := by intros; simp [Finset.smul_sum] }
  have hleft (a : I) (v : ∀ i, Specht (μ i)) : adj a (L v) = v a := by
    change adj a (∑ i, j i (v i)) = _
    rw [map_sum]
    rw [Finset.sum_eq_single a]
    · exact hdiag a (v a)
    · intro b _ hab
      exact hcross a b hab.symm (v b)
    · simp
  have hL : Function.Injective L := by
    intro v w he
    funext a
    have ha := congrArg (adj a) he
    simpa only [hleft] using ha
  simpa only [Module.finrank_pi_fintype, spechtDimension] using
    LinearMap.finrank_le_finrank_of_injective (f := L) hL

theorem subdiagram_dimension_sum_le {m n : ℕ} (hmn : m ≤ n) (lam : Partition n) :
    ∑ μ : {μ : Partition m // μ.1 ≤ lam.1}, spechtDimension μ.1 ≤ spechtDimension lam := by
  let i : Fin m ↪ Fin n := ⟨Fin.castLE hmn, Fin.castLE_injective _⟩
  let ρ := (spechtRepresentation lam).comp (Equiv.Perm.viaEmbeddingHom i)
  apply sum_spechtDimensions_le ρ (fun g => spechtRepresentation_norm lam _) Subtype.val
    Subtype.val_injective
  intro μ
  exact subdiagram_specht_occurs_at μ.1 lam μ.2 i

def standardTableauCount : (n : ℕ) → Partition n → ℕ
  | 0, _ => 1
  | n + 1, lam => ∑ μ : {μ : Partition n // μ.1 ≤ lam.1}, standardTableauCount n μ.1

theorem standardTableauCount_le_spechtDimension (n : ℕ) (lam : Partition n) :
    standardTableauCount n lam ≤ spechtDimension lam := by
  induction n with
  | zero => simp only [standardTableauCount, spechtDimension_empty, le_refl]
  | succ n ih =>
    exact (Finset.sum_le_sum (fun μ _ => ih μ.1)).trans
      (subdiagram_dimension_sum_le (Nat.le_succ n) lam)

end SignedSweeps
end

end OAI
