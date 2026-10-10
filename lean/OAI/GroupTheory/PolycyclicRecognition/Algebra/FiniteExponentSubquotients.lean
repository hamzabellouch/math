import OAI.GroupTheory.PolycyclicRecognition.Algebra.SquareZeroPower
import OAI.GroupTheory.PolycyclicRecognition.Algebra.QuotientLinearAction

namespace OAI

/-! # Finite-exponent actions are detected on an invariant subspace and quotient

An element acting trivially on both pieces differs from the identity by a
square-zero operator. In characteristic zero a positive finite power can
then be the identity only if the element itself is the identity.
-/

noncomputable section
namespace PolycyclicRecognition

variable {K G V : Type*} [Field K] [CharZero K] [Group G]
    [AddCommGroup V] [Module K V]

theorem linear_eq_one_of_finite_power_trivial_subquotient
    (A : V ≃ₗ[K] V) (W : Submodule K V)
    (hfix : ∀ x ∈ W, A x = x) (hquot : ∀ x, A x - x ∈ W)
    (m : ℕ) (hm : 0 < m) (hpow : A ^ m = 1) : A = 1 := by
  let D : Module.End K V := A.toLinearMap - 1
  have hD : D * D = 0 := by
    ext x
    change A (A x - x) - (A x - x) = 0
    rw [hfix _ (hquot x), sub_self]
  have hAD : 1 + D = A.toLinearMap := by simp [D]
  have hp : A.toLinearMap ^ m = 1 := by
    have hh := congrArg LinearEquiv.automorphismGroup.toLinearMapMonoidHom hpow
    change LinearEquiv.automorphismGroup.toLinearMapMonoidHom A ^ m = 1
    simpa only [map_pow, map_one] using hh
  have hz : m • D = 0 := by
    have hh := one_add_pow_of_square_zero D hD m
    rw [hAD, hp] at hh
    exact (add_right_inj (1 : Module.End K V)).mp (by simpa only [add_zero] using hh.symm)
  have hzero : D = 0 := by
    have hh : (m : K) • D = 0 := by simpa only [Nat.cast_smul_eq_nsmul] using hz
    exact (smul_eq_zero.mp hh).resolve_left (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm))
  have he : A.toLinearMap = 1 := sub_eq_zero.mp hzero
  exact LinearEquiv.ext fun x => congrArg (fun T : Module.End K V => T x) he

theorem subquotient_action_pair_injective_of_finite_exponent
    (ρ : G →* (V ≃ₗ[K] V)) (hρ : Function.Injective ρ)
    (W : Submodule K V) (hW : ∀ g : G, ∀ x ∈ W, ρ g x ∈ W)
    (m : ℕ) (hm : 0 < m) (hpow : ∀ g : G, g ^ m = 1) :
    Function.Injective (fun g : G =>
      (invariantSubspaceAction ρ W hW g, quotientLinearAction ρ W hW g)) := by
  let f := (invariantSubspaceAction ρ W hW).prod (quotientLinearAction ρ W hW)
  change Function.Injective f
  apply (injective_iff_map_eq_one f).mpr
  intro g hg
  have hsub : invariantSubspaceAction ρ W hW g = 1 := congrArg Prod.fst hg
  have hq : quotientLinearAction ρ W hW g = 1 := congrArg Prod.snd hg
  have hfix (x : V) (hx : x ∈ W) : ρ g x = x := by
    have hh := congrArg (fun T : W ≃ₗ[K] W => (T ⟨x, hx⟩ : V)) hsub
    exact hh
  have hquot (x : V) : ρ g x - x ∈ W := by
    apply (Submodule.Quotient.mk_eq_zero W).mp
    change W.mkQ (ρ g x - x) = 0
    rw [map_sub]
    have hh := congrArg (fun T : (V ⧸ W) ≃ₗ[K] (V ⧸ W) => T (W.mkQ x)) hq
    change W.mkQ (ρ g x) = W.mkQ x at hh
    rw [hh, sub_self]
  apply hρ
  rw [map_one]
  apply linear_eq_one_of_finite_power_trivial_subquotient (ρ g) W hfix hquot m hm
  rw [← map_pow, hpow, map_one]

end PolycyclicRecognition

end

end OAI
