import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve

theorem finite_recursion_descent (F : ℕ → ℝ) (N₀ R : ℕ) {D H E Fbase : ℝ}
    (hD : 1 ≤ D) (hH : 1 ≤ H) (hE : 0 ≤ E) (hbase0 : 0 ≤ Fbase)
    (hbase : ∀ n ≤ N₀, (n : ℝ) ≤ D → F n ≤ Fbase)
    (hstep : ∀ n ≤ N₀, D < (n : ℝ) →
      ∃ m ≤ N₀, (m : ℝ) ≤ (n : ℝ) / D ∧ F n ≤ H * (F m + E)) :
    ∀ n ≤ N₀, (n : ℝ) ≤ D^R → F n ≤ H^R * (Fbase + (R : ℝ)*E) := by
  have hD0 : 0 < D := by linarith
  have hH0 : 0 ≤ H := by linarith
  induction R with
  | zero =>
    intro n hn hsize
    simpa using hbase n hn (hsize.trans (by simpa using hD))
  | succ R ih =>
    intro n hn hsize
    have hpow : 1 ≤ H^R := one_le_pow₀ hH
    by_cases hsmall : (n : ℝ) ≤ D
    · refine (hbase n hn hsmall).trans ?_
      have hp : 1 ≤ H^(R+1) := one_le_pow₀ hH
      have hb : Fbase ≤ Fbase + ((R+1 : ℕ) : ℝ)*E :=
        le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hE)
      exact hb.trans (le_mul_of_one_le_left (by positivity) hp)
    · obtain ⟨m,hm,hmd,hmF⟩ := hstep n hn (lt_of_not_ge hsmall)
      have hmsize : (m : ℝ) ≤ D^R := by
        calc
          (m : ℝ) ≤ (n : ℝ)/D := hmd
          _ ≤ D^(R+1)/D := div_le_div_of_nonneg_right hsize hD0.le
          _ = D^R := by rw [pow_succ]; field_simp
      have hi := ih m hm hmsize
      calc
        F n ≤ H*(F m+E) := hmF
        _ ≤ H*(H^R*(Fbase+(R:ℝ)*E)+E) :=
          mul_le_mul_of_nonneg_left (add_le_add hi le_rfl) hH0
        _ ≤ H^(R+1)*(Fbase+((R+1:ℕ):ℝ)*E) := by
          have he : E ≤ H^R*E := le_mul_of_one_le_left hE hpow
          have hh := mul_le_mul_of_nonneg_left he hH0
          rw [pow_succ]
          push_cast
          nlinarith

theorem finite_recursion_descent_at (F : ℕ → ℝ) (N₀ R : ℕ) {D H E Fbase : ℝ}
    (hD : 1 ≤ D) (hH : 1 ≤ H) (hE : 0 ≤ E) (hbase0 : 0 ≤ Fbase)
    (hsize : (N₀ : ℝ) ≤ D^R)
    (hbase : ∀ n ≤ N₀, (n : ℝ) ≤ D → F n ≤ Fbase)
    (hstep : ∀ n ≤ N₀, D < (n : ℝ) →
      ∃ m ≤ N₀, (m : ℝ) ≤ (n : ℝ) / D ∧ F n ≤ H * (F m + E)) :
    F N₀ ≤ H^R * (Fbase+(R:ℝ)*E) :=
  finite_recursion_descent F N₀ R hD hH hE hbase0 hbase hstep N₀ le_rfl hsize

end Ostmann.QuadraticSieve

end

end OAI
