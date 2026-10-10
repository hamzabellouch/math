import OAI.Analysis.CircleDomains.Selection.PositiveJumpCount
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.Filter.AtTopBot.Basic

namespace OAI

/-! The bounded number of jumps and finite set of old disk labels admit
a subsequence with one fixed pattern. New disk labels are not frozen. -/

open Set Function Filter

namespace CircleDomainRigidity

theorem exists_constant_finite_pattern_subsequence
    {I : Type*} [Finite I] (f : ℕ → I) :
    ∃p : I, ∃s : ℕ → ℕ, StrictMono s ∧ ∀k, f (s k) = p := by
  obtain ⟨p, hp⟩ := Finite.exists_infinite_fiber f
  have hinf : (f ⁻¹' {p}).Infinite := infinite_coe_iff.mp hp
  obtain ⟨s, hs, heq⟩ := Nat.exists_strictMono_subsequence (fun N => by
    obtain ⟨k, hk, hNk⟩ := hinf.exists_gt N
    exact ⟨k, hNk, hk⟩)
  exact ⟨p, s, hs, heq⟩

abbrev BoundedJumpPattern (I : Type*) (N : ℕ) :=
  Σn : Fin (N+1), Fin n.val → Option I

theorem exists_fixed_bounded_jump_pattern
    {I : Type*} [Finite I] (N : ℕ) (f : ℕ → BoundedJumpPattern I N) :
    ∃p : BoundedJumpPattern I N, ∃s : ℕ → ℕ, StrictMono s ∧ ∀k, f (s k) = p :=
  exists_constant_finite_pattern_subsequence f

end CircleDomainRigidity

end OAI
