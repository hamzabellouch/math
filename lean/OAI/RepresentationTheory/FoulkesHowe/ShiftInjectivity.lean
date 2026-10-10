import Mathlib

namespace OAI

noncomputable section

namespace Problem346
namespace ShiftInjectivity

variable {K M : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M]

/-- A weight-raising operator increases the weight of its iterates by two. -/
theorem weight_pow (E H : Module.End K M)
    (hHE : ∀ z, H (E z) = E (H z) + (2 : K) • E z)
    (x : M) (w : K) (hx : H x = w • x) (n : ℕ) :
    H ((E ^ n) x) = (w + 2 * (n : K)) • (E ^ n) x := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, hHE, ih, map_smul,
      ← add_smul]
    congr 1
    push_cast
    ring

/-- The lowering operator on a string generated from a vector in its kernel. -/
theorem lowering_pow (D E H : Module.End K M)
    (hDE : ∀ z, D (E z) = E (D z) - H z)
    (hHE : ∀ z, H (E z) = E (H z) + (2 : K) • E z)
    (x : M) (w : K) (hx : H x = w • x) (hDx : D x = 0) (n : ℕ) :
    D ((E ^ (n + 1)) x) =
      (-((n + 1 : K) * (w + n))) • (E ^ n) x := by
  induction n with
  | zero =>
    simp [hDE, hDx, hx]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, hDE, ih,
      weight_pow E H hHE x w hx (n + 1), map_smul]
    rw [← Module.End.mul_apply, ← pow_succ', ← sub_smul]
    congr 1
    push_cast
    ring

/-- Positive-weight vectors killed by a lowering operator vanish provided that the
opposite operator acts nilpotently on that vector. This is the algebraic form of
positive-weight differential injectivity and requires no inner product. -/
theorem eq_zero_of_positive_weight (D E H : Module.End K M)
    (hDE : ∀ z, D (E z) = E (D z) - H z)
    (hHE : ∀ z, H (E z) = E (H z) + (2 : K) • E z)
    (x : M) (w : ℕ) (hw : 0 < w) (hx : H x = (w : K) • x)
    (hDx : D x = 0) (hnil : ∃ N : ℕ, (E ^ N) x = 0) : x = 0 := by
  obtain ⟨N, hN⟩ := hnil
  induction N with
  | zero => simpa using hN
  | succ n ih =>
    apply ih
    have h := lowering_pow D E H hDE hHE x (w : K) hx hDx n
    rw [hN, map_zero] at h
    have hc : (-((n + 1 : K) * ((w : K) + n))) ≠ 0 := by
      apply neg_ne_zero.mpr
      apply mul_ne_zero
      · exact_mod_cast (Nat.succ_ne_zero n)
      · have : w + n ≠ 0 := by omega
        exact_mod_cast this
    exact (smul_eq_zero.mp h.symm).resolve_left hc

end ShiftInjectivity
end Problem346

end

end OAI
