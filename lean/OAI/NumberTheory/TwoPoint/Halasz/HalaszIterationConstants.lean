import OAI.NumberTheory.TwoPoint.Halasz.HalaszIterationScale

namespace OAI

/-! Explicit constants for the classical iteration. -/
namespace TwoPointCorrelations

def halaszIterationBase (R₀ k : ℕ) : ℕ :=
  k.factorial+(halaszIterationThreshold R₀ k)^(k+k*(k-1)/2)+
    2*(2*(k^2*k)+1)*k^k*32^(k*(k-1)/2)+1

def halaszIterationConstant (R₀ k n : ℕ) : ℕ :=
  (halaszIterationBase R₀ k)^(n+1)*32^(k*n*(n+1))

lemma halasz_iteration_base_bounds (R₀ k : ℕ) :
    1≤halaszIterationBase R₀ k ∧ k.factorial≤halaszIterationBase R₀ k ∧
    (halaszIterationThreshold R₀ k)^(k+k*(k-1)/2)≤halaszIterationBase R₀ k ∧
    2*(2*(k^2*k)+1)*k^k*32^(k*(k-1)/2)≤halaszIterationBase R₀ k := by
  unfold halaszIterationBase
  omega

lemma halasz_iteration_constant_ge_base (R₀ k n : ℕ) :
    halaszIterationBase R₀ k≤halaszIterationConstant R₀ k n := by
  have hb := (halasz_iteration_base_bounds R₀ k).1
  have hp : halaszIterationBase R₀ k≤(halaszIterationBase R₀ k)^(n+1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hb (by omega : 1≤n+1)
  have h32 : 1≤(32:ℕ)^(k*n*(n+1)) := Nat.one_le_pow _ _ (by decide)
  exact hp.trans (Nat.le_mul_of_pos_right _ (by omega))

lemma halasz_iteration_constant_zero (R₀ k : ℕ) :
    halaszIterationConstant R₀ k 0=halaszIterationBase R₀ k := by
  simp [halaszIterationConstant]

theorem halasz_iteration_constant_step (R₀ k n : ℕ) :
    halaszIterationConstant R₀ k n *
      (2*(2*(k^2*k)+1)*k^k*32^(2*((n+1)*k)+k*(k-1)/2)) ≤
        halaszIterationConstant R₀ k (n+1) := by
  have hc := (halasz_iteration_base_bounds R₀ k).2.2.2
  have hfactor : 2*(2*(k^2*k)+1)*k^k*32^(2*((n+1)*k)+k*(k-1)/2) =
      (2*(2*(k^2*k)+1)*k^k*32^(k*(k-1)/2))*32^(2*((n+1)*k)) := by
    rw [pow_add]
    ring
  rw [hfactor]
  calc
    _ ≤ halaszIterationConstant R₀ k n *
        (halaszIterationBase R₀ k*32^(2*((n+1)*k))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hc)
    _ = halaszIterationConstant R₀ k (n+1) := by
      unfold halaszIterationConstant
      rw [pow_succ]
      have he : k*n*(n+1)+2*((n+1)*k)=k*(n+1)*(n+1+1) := by ring
      rw [← he,pow_add]
      ring

end TwoPointCorrelations

end OAI
