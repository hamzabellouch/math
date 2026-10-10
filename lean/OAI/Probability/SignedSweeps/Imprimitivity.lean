import OAI.Probability.SignedSweeps.WordTensorBasis

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G E F L : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [FiniteDimensional ℂ L]

def fiberAverage (H : Subgroup G) (ρ : Representation ℂ G L)
    (τ : Representation ℂ H E) (σ : Representation ℂ G F) (j : E →ₗ[ℂ] F) :
    Representation.IntertwiningMap (ρ.comp H.subtype) τ →ₗ[ℂ]
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

omit [FiniteDimensional ℂ E] in
lemma fiberAverage_compression (H : Subgroup G) (ρ : Representation ℂ G L)
    (τ : Representation ℂ H E) (σ : Representation ℂ G F)
    (j : E →ₗ[ℂ] F) (q : F →ₗ[ℂ] E)
    (hq : q ∘ₗ j = LinearMap.id)
    (hj : ∀ h : H, σ h.1 ∘ₗ j = j ∘ₗ τ h)
    (hoff : ∀ g ∉ H, q ∘ₗ σ g ∘ₗ j = 0)
    (f : Representation.IntertwiningMap (ρ.comp H.subtype) τ) (x : L) :
    q (fiberAverage H ρ τ σ j f x) = (Fintype.card H : ℂ) • f x := by
  change q (mixedConjugationSum ρ σ (j ∘ₗ f.toLinearMap) x) = _
  simp only [mixedConjugationSum, LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
  change (∑ g : G, q (σ g (j (f (ρ g⁻¹ x))))) = _
  have hterm (g : G) : q (σ g (j (f (ρ g⁻¹ x)))) = if g ∈ H then f x else 0 := by
    split_ifs with hg
    · have he := LinearMap.congr_fun (hj ⟨g,hg⟩) (f (ρ g⁻¹ x))
      change σ g (j (f (ρ g⁻¹ x))) = j (τ ⟨g,hg⟩ (f (ρ g⁻¹ x))) at he
      rw [he]
      change (q ∘ₗ j) (τ ⟨g,hg⟩ (f (ρ g⁻¹ x))) = f x
      rw [hq, LinearMap.id_apply, ← f.isIntertwining]
      change f (ρ g (ρ g⁻¹ x)) = _
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    · exact LinearMap.congr_fun (hoff g hg) _
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun g : G => g ∈ H) (F := inferInstance) (Finset.univ.filter (· ∈ H)) (by simp)
    (fun _ : G => f x)]
  simp [Nat.cast_smul_eq_nsmul]

omit [FiniteDimensional ℂ E] in
theorem fiberAverage_injective (H : Subgroup G) (ρ : Representation ℂ G L)
    (τ : Representation ℂ H E) (σ : Representation ℂ G F)
    (j : E →ₗ[ℂ] F) (q : F →ₗ[ℂ] E)
    (hq : q ∘ₗ j = LinearMap.id)
    (hj : ∀ h : H, σ h.1 ∘ₗ j = j ∘ₗ τ h)
    (hoff : ∀ g ∉ H, q ∘ₗ σ g ∘ₗ j = 0) :
    Function.Injective (fiberAverage H ρ τ σ j) := by
  intro f k hfk
  apply Representation.IntertwiningMap.ext
  ext x
  have he := congrArg (fun A : Representation.IntertwiningMap ρ σ => q (A x)) hfk
  rw [fiberAverage_compression H ρ τ σ j q hq hj hoff,
    fiberAverage_compression H ρ τ σ j q hq hj hoff] at he
  exact smul_right_injective E (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) he

omit [FiniteDimensional ℂ E] in
theorem fiber_multiplicity_le (H : Subgroup G) (ρ : Representation ℂ G L)
    (τ : Representation ℂ H E) (σ : Representation ℂ G F)
    (j : E →ₗ[ℂ] F) (q : F →ₗ[ℂ] E)
    (hq : q ∘ₗ j = LinearMap.id)
    (hj : ∀ h : H, σ h.1 ∘ₗ j = j ∘ₗ τ h)
    (hoff : ∀ g ∉ H, q ∘ₗ σ g ∘ₗ j = 0) :
    finrank ℂ (Representation.IntertwiningMap (ρ.comp H.subtype) τ) ≤
      finrank ℂ (Representation.IntertwiningMap ρ σ) :=
  LinearMap.finrank_le_finrank_of_injective (fiberAverage_injective H ρ τ σ j q hq hj hoff)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G E : Type*} [Monoid G] [AddCommGroup E] [Module ℂ E]

def projectionSubrepresentation (ρ : Representation ℂ G E) (P : E →ₗ[ℂ] E)
    (hcomm : ∀ g, ρ g * P = P * ρ g) : Subrepresentation ρ where
  toSubmodule := P.range
  apply_mem_toSubmodule g x hx := by
    obtain ⟨y,rfl⟩ := hx
    exact ⟨ρ g y, (LinearMap.congr_fun (hcomm g) y).symm⟩

end SignedSweeps
end

end OAI
