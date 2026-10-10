import OAI.GroupTheory.FiniteLattice.PerfectPreimage
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace OAI

/-! Equivariance of the least normal preimage of a perfect subgroup. -/
namespace FiniteLattice.CommonCore

variable {M H : Type*} [Group M] [Group H]

/-- Leastness forces invariance for a prescribed image, not merely image top. -/
theorem least_image_stable
    (f : M →* H) (J : Subgroup H) (Q : Subgroup M) [Q.Normal]
    (himage : Q.map f = J)
    (hleast : ∀ B : Subgroup M, B.Normal → J ≤ B.map f → Q ≤ B)
    (a : M ≃* M) (b : H ≃* H)
    (hJ : ∀ y ∈ J, b y ∈ J)
    (hcompat : ∀ x, f (a x) = b (f x)) :
    ∀ x ∈ Q, a x ∈ Q := by
  have hcover : J ≤ (Q.comap a.toMonoidHom).map f := by
    intro y hy
    have hby : b y ∈ Q.map f := by
      rw [himage]
      exact hJ y hy
    obtain ⟨x, hx, hfx⟩ := hby
    refine ⟨a.symm x, ?_, ?_⟩
    · change a (a.symm x) ∈ Q
      rw [a.apply_symm_apply]
      exact hx
    · apply b.injective
      calc
        b (f (a.symm x)) = f (a (a.symm x)) := (hcompat _).symm
        _ = f x := congrArg f (a.apply_symm_apply x)
        _ = b y := hfx
  exact fun x hx => hleast _ inferInstance hcover hx

/-- A compatible pair of automorphisms preserving the prescribed image
also preserves its least normal preimage. -/
theorem least_image_map_eq
    (f : M →* H) (J : Subgroup H) (Q : Subgroup M) [Q.Normal]
    (himage : Q.map f = J)
    (hleast : ∀ B : Subgroup M, B.Normal → J ≤ B.map f → Q ≤ B)
    (a : M ≃* M) (b : H ≃* H)
    (hJ : J.map b.toMonoidHom = J)
    (hcompat : ∀ x, f (a x) = b (f x)) :
    Q.map a.toMonoidHom = Q := by
  have hb : ∀ y ∈ J, b y ∈ J := by
    intro y hy
    rw [← hJ]
    exact ⟨y, hy, rfl⟩
  have hbi : ∀ y ∈ J, b.symm y ∈ J := by
    intro y hy
    rw [← hJ] at hy
    obtain ⟨z, hz, hz'⟩ := hy
    have : b.symm y = z := by
      rw [← hz']
      change b.symm (b z) = z
      exact b.symm_apply_apply z
    rwa [this]
  have hinv : ∀ y, f (a.symm y) = b.symm (f y) := by
    intro y
    apply b.injective
    rw [b.apply_symm_apply]
    exact (hcompat (a.symm y)).symm.trans
      (congrArg f (a.apply_symm_apply y))
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact least_image_stable f J Q himage hleast a b hb hcompat x hx
  · intro x hx
    exact ⟨a.symm x,
      least_image_stable f J Q himage hleast a.symm b.symm hbi hinv x hx,
      a.apply_symm_apply x⟩

/-- A perfect normal subgroup in the image has a least normal preimage,
invariant under every compatible pair of automorphisms preserving the image. -/
theorem exists_equivariant_least_preimage [Finite M]
    (f : M →* H) (J : Subgroup H) [J.Normal] [Group.IsPerfect J]
    (hJ : J ≤ f.range) :
    ∃ Q : Subgroup M, Q.Normal ∧ Q.map f = J ∧
      (∀ B : Subgroup M, B.Normal → J ≤ B.map f → Q ≤ B) ∧
      (∀ (a : M ≃* M) (b : H ≃* H), J.map b.toMonoidHom = J →
        (∀ x, f (a x) = b (f x)) → Q.map a.toMonoidHom = Q) := by
  obtain ⟨Q, hQN, hQI, hleast⟩ :=
    FiniteLattice.exists_least_normal_perfect_preimage f J hJ
  let : Q.Normal := hQN
  exact ⟨Q, hQN, hQI, hleast, fun a b hb hc =>
    least_image_map_eq f J Q hQI hleast a b hb hc⟩

end FiniteLattice.CommonCore

end OAI
