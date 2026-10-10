import OAI.Probability.SignedSweeps.MarkedWords

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G H E F L : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [FiniteDimensional ℂ L]

def embeddedFiberAverage (i : H →* G) (ρ : Representation ℂ G L)
    (τ : Representation ℂ H E) (σ : Representation ℂ G F) (j : E →ₗ[ℂ] F) :
    Representation.IntertwiningMap (ρ.comp i) τ →ₗ[ℂ]
      Representation.IntertwiningMap ρ σ where
  toFun f := (mixedConjugationSum ρ σ (j ∘ₗ f.toLinearMap)).intertwiningMap_of_isIntertwiningMap
    ρ σ (mixedConjugationSum_intertwines ρ σ _)
  map_add' f k := by
    apply Representation.IntertwiningMap.ext
    ext x
    change mixedConjugationSum ρ σ (j ∘ₗ (f.toLinearMap + k.toLinearMap)) x =
      mixedConjugationSum ρ σ (j ∘ₗ f.toLinearMap) x +
        mixedConjugationSum ρ σ (j ∘ₗ k.toLinearMap) x
    simp only [mixedConjugationSum, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c f := by
    apply Representation.IntertwiningMap.ext
    ext x
    change mixedConjugationSum ρ σ (j ∘ₗ (c • f.toLinearMap)) x =
      c • mixedConjugationSum ρ σ (j ∘ₗ f.toLinearMap) x
    simp only [mixedConjugationSum, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, map_smul, Finset.smul_sum]

lemma embeddedFiberAverage_compression
    {G H E F L : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [FiniteDimensional ℂ L]
    (i : H →* G) (hi : Function.Injective i)
    (ρ : Representation ℂ G L) (τ : Representation ℂ H E) (σ : Representation ℂ G F)
    (j : E →ₗ[ℂ] F) (q : F →ₗ[ℂ] E)
    (hq : q ∘ₗ j = LinearMap.id)
    (hj : ∀ h, σ (i h) ∘ₗ j = j ∘ₗ τ h)
    (hoff : ∀ g ∉ Set.range i, q ∘ₗ σ g ∘ₗ j = 0)
    (f : Representation.IntertwiningMap (ρ.comp i) τ) (x : L) :
    q (embeddedFiberAverage i ρ τ σ j f x) = (Fintype.card H : ℂ) • f x := by
  change q (mixedConjugationSum ρ σ (j ∘ₗ f.toLinearMap) x) = _
  simp only [mixedConjugationSum, LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
  change (∑ g : G, q (σ g (j (f (ρ g⁻¹ x))))) = _
  have hterm (g : G) : q (σ g (j (f (ρ g⁻¹ x)))) =
      if g ∈ Finset.univ.image i then f x else 0 := by
    split_ifs with hg
    · obtain ⟨h,_,rfl⟩ := Finset.mem_image.mp hg
      have he := LinearMap.congr_fun (hj h) (f (ρ (i h)⁻¹ x))
      change σ (i h) (j (f (ρ (i h)⁻¹ x))) = j (τ h (f (ρ (i h)⁻¹ x))) at he
      rw [he]
      change (q ∘ₗ j) (τ h (f (ρ (i h)⁻¹ x))) = f x
      rw [hq, LinearMap.id_apply, ← f.isIntertwining]
      change f (ρ (i h) (ρ (i h)⁻¹ x)) = _
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    · exact LinearMap.congr_fun (hoff g (by simpa using hg)) _
  simp_rw [hterm]
  rw [Fintype.sum_extend_by_zero, Finset.sum_image (fun _ _ _ _ he => hi he)]
  simp [Nat.cast_smul_eq_nsmul]

lemma embeddedFiberAverage_injective (i : H →* G) (hi : Function.Injective i)
    (ρ : Representation ℂ G L) (τ : Representation ℂ H E) (σ : Representation ℂ G F)
    (j : E →ₗ[ℂ] F) (q : F →ₗ[ℂ] E)
    (hq : q ∘ₗ j = LinearMap.id)
    (hj : ∀ h, σ (i h) ∘ₗ j = j ∘ₗ τ h)
    (hoff : ∀ g ∉ Set.range i, q ∘ₗ σ g ∘ₗ j = 0) :
    Function.Injective (embeddedFiberAverage i ρ τ σ j) := by
  intro f k hfk
  apply Representation.IntertwiningMap.ext
  ext x
  have he := congrArg (fun A : Representation.IntertwiningMap ρ σ => q (A x)) hfk
  rw [embeddedFiberAverage_compression i hi ρ τ σ j q hq hj hoff,
    embeddedFiberAverage_compression i hi ρ τ σ j q hq hj hoff] at he
  exact smul_right_injective E (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) he

theorem embedded_fiber_multiplicity_le (i : H →* G) (hi : Function.Injective i)
    (ρ : Representation ℂ G L) (τ : Representation ℂ H E) (σ : Representation ℂ G F)
    (j : E →ₗ[ℂ] F) (q : F →ₗ[ℂ] E)
    (hq : q ∘ₗ j = LinearMap.id)
    (hj : ∀ h, σ (i h) ∘ₗ j = j ∘ₗ τ h)
    (hoff : ∀ g ∉ Set.range i, q ∘ₗ σ g ∘ₗ j = 0) :
    finrank ℂ (Representation.IntertwiningMap (ρ.comp i) τ) ≤
      finrank ℂ (Representation.IntertwiningMap ρ σ) :=
  LinearMap.finrank_le_finrank_of_injective
    (embeddedFiberAverage_injective i hi ρ τ σ j q hq hj hoff)

end SignedSweeps
end

end OAI
