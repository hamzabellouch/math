import OAI.Probability.SignedSweeps.PolytabloidNonzero
import OAI.Probability.SignedSweeps.YoungLemma

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

@[simp] lemma complexSign_inv {n : ℕ} (g : SymmetricGroup n) :
    complexSign n g⁻¹ = complexSign n g := by
  simp [complexSign]

lemma polytabloid_left_column {n : ℕ} (lam : Partition n)
    (c : colSubgroup lam) (g : SymmetricGroup n) :
    polytabloid lam (c.1 * g) = complexSign n c.1 * polytabloid lam g := by
  have h := congrArg (fun f : RegularSpace n => f g) (polytabloid_column_action lam c⁻¹)
  simpa only [regularRepresentation_apply, Subgroup.coe_inv, inv_inv, PiLp.smul_apply,
    smul_eq_mul, complexSign_inv] using h

lemma row_column_vector_eq {n : ℕ} (lam : Partition n) (f : RegularSpace n)
    (hr : ∀ (a : rowSubgroup lam) g, f (g * a.1) = f g)
    (hc : ∀ (c : colSubgroup lam) g, f (c.1 * g) = complexSign n c.1 * f g) :
    f = f 1 • polytabloid lam := by
  ext g
  change f g = f 1 * polytabloid lam g
  by_cases ht : ∀ x y, lam.rowOf x = lam.rowOf y → lam.colOf (g x) = lam.colOf (g y) → x = y
  · obtain ⟨c, a, rfl⟩ := young_factorization lam g ht
    rw [hr, polytabloid_right_row, ← mul_one c.1, hc, polytabloid_left_column,
      polytabloid_at_one]
    ring
  · obtain ⟨a, c, he, hs⟩ := young_collision lam g ht
    have hf : f g = 0 := by
      have h := hc c g
      rw [he, hr, hs, neg_one_mul] at h
      linear_combination h / 2
    have hp : polytabloid lam g = 0 := by
      have h := polytabloid_left_column lam c g
      rw [he, polytabloid_right_row, hs, neg_one_mul] at h
      linear_combination h / 2
    simp only [hf, hp, mul_zero]

lemma spechtGenerator_column_action {n : ℕ} (lam : Partition n) (c : colSubgroup lam) :
    spechtRepresentation lam c.1 (spechtGenerator lam) = complexSign n c.1 • spechtGenerator lam := by
  apply Subtype.ext
  exact polytabloid_column_action lam c

lemma specht_hom_ext {n : ℕ} (lam : Partition n)
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E)
    (f g : Representation.IntertwiningMap (spechtRepresentation lam) ρ)
    (h : f (spechtGenerator lam) = g (spechtGenerator lam)) : f = g := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  have haux : ∀ v (hv : v ∈ (spechtSubrepresentation lam).toSubmodule),
      f ⟨v, hv⟩ = g ⟨v, hv⟩ := by
    intro v hv
    change v ∈ Submodule.span ℂ _ at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, rfl⟩ := hv
      change f (spechtRepresentation lam a (spechtGenerator lam)) =
        g (spechtRepresentation lam a (spechtGenerator lam))
      rw [f.isIntertwining, g.isIntertwining, h]
    | zero => exact (map_zero f).trans (map_zero g).symm
    | add x y hx hy hx' hy' =>
      change x ∈ (spechtSubrepresentation lam).toSubmodule at hx
      change y ∈ (spechtSubrepresentation lam).toSubmodule at hy
      change f (⟨x, hx⟩ + ⟨y, hy⟩) = g (⟨x, hx⟩ + ⟨y, hy⟩)
      exact (map_add f (show Specht lam from ⟨x, hx⟩) (show Specht lam from ⟨y, hy⟩)).trans
        ((congrArg₂ (· + ·) hx' hy').trans (map_add g _ _).symm)
    | smul a x hx hx' =>
      change x ∈ (spechtSubrepresentation lam).toSubmodule at hx
      change f (a • (⟨x, hx⟩ : Specht lam)) = g (a • (⟨x, hx⟩ : Specht lam))
      exact (map_smul f a (show Specht lam from ⟨x, hx⟩)).trans
        ((congrArg (a • ·) hx').trans (map_smul g _ _).symm)
  exact haux (spechtInclusion lam x) x.property

lemma specht_endomorphism_scalar {n : ℕ} (lam : Partition n)
    (f : Representation.IntertwiningMap (spechtRepresentation lam) (spechtRepresentation lam)) :
    ∃ z : ℂ, f = z • (1 : Representation.IntertwiningMap (spechtRepresentation lam)
      (spechtRepresentation lam)) := by
  let v := f (spechtGenerator lam)
  have hh : spechtInclusion lam v = (spechtInclusion lam v) 1 • polytabloid lam := by
    apply row_column_vector_eq
    · exact specht_right_row lam v
    · intro c g
      have he : spechtRepresentation lam (c⁻¹).1 v = complexSign n (c⁻¹).1 • v := by
        rw [← f.isIntertwining, spechtGenerator_column_action, map_smul]
      have h := congrArg (fun x => (spechtInclusion lam x) g) he
      change (spechtInclusion lam v) ((c⁻¹).1⁻¹ * g) =
        complexSign n (c⁻¹).1 * (spechtInclusion lam v) g at h
      simpa only [Subgroup.coe_inv, inv_inv, complexSign_inv] using h
  refine ⟨(spechtInclusion lam v) 1, specht_hom_ext lam (spechtRepresentation lam) _ _ ?_⟩
  apply Subtype.ext
  exact hh

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma invariant_starProjection_intertwines {G E : Type*} [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ G E) (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (S : Subrepresentation ρ) (g : G) (x : E) :
    S.toSubmodule.starProjection (ρ g x) = ρ g (S.toSubmodule.starProjection x) := by
  apply S.toSubmodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact S.apply_mem_toSubmodule g (S.toSubmodule.starProjection_apply_mem x)
  · intro w hw
    rw [← map_sub, representation_inner_inverse ρ hρ]
    exact S.toSubmodule.starProjection_inner_eq_zero x _ (S.apply_mem_toSubmodule g⁻¹ hw)

lemma irreducible_of_scalar_commutant {G E : Type*} [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [Nontrivial E]
    (ρ : Representation ℂ G E) (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (hscalar : ∀ f : Representation.IntertwiningMap ρ ρ,
      ∃ z : ℂ, f = z • (1 : Representation.IntertwiningMap ρ ρ)) :
    ρ.IsIrreducible := by
  have hb : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    have hh := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top (α := Submodule ℂ E) hh
  let : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, hb⟩⟩
  refine ⟨?_⟩
  intro S
  let p : Representation.IntertwiningMap ρ ρ :=
    S.toSubmodule.starProjection.toLinearMap.intertwiningMap_of_isIntertwiningMap ρ ρ
      (invariant_starProjection_intertwines ρ hρ S)
  obtain ⟨z, hz⟩ := hscalar p
  have hp (x : E) : S.toSubmodule.starProjection x = z • x :=
    congrArg (fun f : Representation.IntertwiningMap ρ ρ => f x) hz
  have hid (x : E) : (z * z) • x = z • x := by
    rw [mul_smul, ← hp, ← hp]
    exact S.toSubmodule.starProjection_eq_self_iff.mpr (S.toSubmodule.starProjection_apply_mem x)
  have hc : z * (z - 1) = 0 := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    have he : (z * (z - 1)) • x = 0 := by
      rw [mul_sub, mul_one, sub_smul, hid, sub_self]
    exact (smul_eq_zero.mp he).resolve_right hx
  rcases mul_eq_zero.mp hc with hz0 | hz1
  · left
    apply Subrepresentation.toSubmodule_injective
    apply eq_bot_iff.mpr
    intro x hx
    have he := S.toSubmodule.starProjection_eq_self_iff.mpr hx
    rw [hp, hz0, zero_smul] at he
    exact he.symm
  · right
    apply Subrepresentation.toSubmodule_injective
    apply eq_top_iff.mpr
    intro x hx
    rw [sub_eq_zero] at hz1
    have he := S.toSubmodule.starProjection_apply_mem x
    rwa [hp, hz1, one_smul] at he

theorem specht_irreducible {n : ℕ} (lam : Partition n) :
    (spechtRepresentation lam).IsIrreducible :=
  irreducible_of_scalar_commutant _ (spechtRepresentation_norm lam)
    (specht_endomorphism_scalar lam)

end SignedSweeps
end

end OAI
