import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Gadgets.AdaptivePathsLemmas

namespace OAI

section

/-!
Uniform injective parameter maps induce the uniform law on subspaces of the
specified rank.  The proof uses actual transitivity of ambient linear
automorphisms on injections, not an assumed distributional premise.
-/

noncomputable section

open scoped BigOperators
open Module
open UniqueGamesTheorem.Gadget.Orientation

namespace UniqueGamesTheorem.Quadratic.UniformSubspaces

variable {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- A linear parameter map with its injectivity proof. -/
def Injection (K V W : Type*) [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] :=
  {J : V →ₗ[K] W // Function.Injective J}

instance injectionAction : MulAction (W ≃ₗ[K] W) (Injection K V W) where
  smul a J := ⟨a.toLinearMap.comp J.val, a.injective.comp J.property⟩
  one_smul J := by
    apply Subtype.ext
    ext x
    rfl
  mul_smul a b J := by
    apply Subtype.ext
    ext x
    rfl

omit [FiniteDimensional K W] in
/-- Every two injections are carried to each other by an automorphism of the
ambient space: extend the isomorphism between their two images. -/
theorem injection_transitive (J₁ J₂ : Injection K V W) :
    ∃ a : W ≃ₗ[K] W, a • J₁ = J₂ := by
  let e₁ := LinearEquiv.ofInjective J₁.val J₁.property
  let e₂ := LinearEquiv.ofInjective J₂.val J₂.property
  let e : LinearMap.range J₁.val ≃ₗ[K] LinearMap.range J₂.val := e₁.symm.trans e₂
  obtain ⟨a, ha⟩ := Submodule.exists_linearEquiv_restrict_eq e
  refine ⟨a, ?_⟩
  apply Subtype.ext
  ext x
  have h := (ha (e₁ x)).symm
  change a (J₁.val x) = ((e₂ (e₁.symm (e₁ x))) : W) at h
  change a (J₁.val x) = J₂.val x
  simpa only [LinearEquiv.symm_apply_apply, e₂, LinearEquiv.ofInjective_apply] using h

/-- The image has the dimension of the parameter space. -/
def image (J : Injection K V W) : RankSpace K W (finrank K V) :=
  ⟨LinearMap.range J.val, LinearMap.finrank_range_of_inj J.property⟩

omit [FiniteDimensional K V] [FiniteDimensional K W] in
theorem image_action (a : W ≃ₗ[K] W) (J : Injection K V W) :
    image (a • J) = a • image J := by
  apply Subtype.ext
  exact LinearMap.range_comp J.val a.toLinearMap

variable [Fintype (W ≃ₗ[K] W)] [Fintype (Injection K V W)]
    [Fintype (RankSpace K W (finrank K V))]

/-- Exact uniform image law, conditional only on injectivity of the map. -/
theorem mean_image (J₀ : Injection K V W) (f : RankSpace K W (finrank K V) → ℚ) :
    (∑ J : Injection K V W, f (image J)) / Fintype.card (Injection K V W) =
      (∑ S : RankSpace K W (finrank K V), f S) /
        Fintype.card (RankSpace K W (finrank K V)) := by
  have h := mean_action J₀ (injection_transitive J₀) (fun J => f (image J))
  simp_rw [image_action] at h
  exact h.symm.trans (mean_oriented_subspace (image J₀) f)

/-- Indicator specialization of the exact law, without assuming genericity
or independence of a subsequently chosen lift. -/
theorem bad_image_count_ratio (J₀ : Injection K V W)
    (Bad : RankSpace K W (finrank K V) → Prop) :
    (Nat.card {J : Injection K V W // Bad (image J)} : ℚ) /
        Fintype.card (Injection K V W) =
      (Nat.card {S : RankSpace K W (finrank K V) // Bad S} : ℚ) /
        Fintype.card (RankSpace K W (finrank K V)) := by
  classical
  have h := mean_image J₀ (fun S => if Bad S then 1 else 0)
  simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using h

/-- An unconditional bad-parameter count bound transfers after conditioning
on injectivity, paying exactly the usual `1/(1-β)` factor.  The premises are
ordinary count inequalities and can come from polynomial union bounds. -/
theorem bad_subspace_bound (J₀ : Injection K V W)
    (Bad : RankSpace K W (finrank K V) → Prop) (α β : ℚ) (hα : 0 ≤ α) (hβ : β < 1)
    (hbad : (Nat.card {J : Injection K V W // Bad (image J)} : ℚ) ≤
      α * Nat.card (V →ₗ[K] W))
    (hinj : (1 - β) * Nat.card (V →ₗ[K] W) ≤ Fintype.card (Injection K V W)) :
    (Nat.card {S : RankSpace K W (finrank K V) // Bad S} : ℚ) /
        Fintype.card (RankSpace K W (finrank K V)) ≤ α / (1 - β) := by
  rw [← bad_image_count_ratio J₀ Bad]
  have : Nonempty (Injection K V W) := ⟨J₀⟩
  have hi : (0 : ℚ) < Fintype.card (Injection K V W) := by
    exact_mod_cast Fintype.card_pos
  have hd : 0 < 1 - β := sub_pos.mpr hβ
  apply (div_le_div_iff₀ hi hd).mpr
  calc
    (Nat.card {J : Injection K V W // Bad (image J)} : ℚ) * (1 - β) ≤
        (α * Nat.card (V →ₗ[K] W)) * (1 - β) :=
      mul_le_mul_of_nonneg_right hbad hd.le
    _ = α * ((1 - β) * Nat.card (V →ₗ[K] W)) := by ring
    _ ≤ α * Fintype.card (Injection K V W) := mul_le_mul_of_nonneg_left hinj hα

end UniqueGamesTheorem.Quadratic.UniformSubspaces

end

end

end OAI
