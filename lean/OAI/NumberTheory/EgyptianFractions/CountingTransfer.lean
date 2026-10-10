import Mathlib

namespace OAI
noncomputable section
open Filter
open scoped Topology
namespace Problem337
/-- Taking two logarithms of a natural doubly exponential lower bound. -/
theorem loglog_lower_of_two_pow_two_pow {t N : ℕ} (hN : 2 ^ (2 ^ t) ≤ N) :
    (t : ℝ) * Real.log 2 + Real.log (Real.log 2) ≤ Real.log (Real.log (N : ℝ)) := by
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hcast : (2 : ℝ) ^ (2 ^ t) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ (2 ^ t)) hcast
  rw [Real.log_pow] at hlog
  have hpre : 0 < ((2 ^ t : ℕ) : ℝ) * Real.log 2 := mul_pos (by positivity) hl2
  have hll := Real.log_le_log hpre hlog
  rw [Real.log_mul (by positivity : ((2 ^ t : ℕ) : ℝ) ≠ 0) (ne_of_gt hl2)] at hll
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using hll

/-- A supply of exponential counts at logarithmically short lengths transfers
by padding monotonicity to a linear double-log lower bound at every long length. -/
theorem counting_lower_transfer (f : ℕ → ℕ) {B : ℝ} (hB : 0 < B)
    (hmono : ∀ i j : ℕ, 2 ≤ i → i ≤ j → f i ≤ f j)
    (hsupply : ∀ᶠ r : ℕ in atTop, ∃ ell : ℕ, 2 ≤ ell ∧
      (ell : ℝ) ≤ B * Real.log (r : ℝ) ∧ 2 ^ (r - 1) ≤ f ell) :
    ∀ᶠ k : ℕ in atTop,
      (1 / (2 * B)) * (k : ℝ) ≤ Real.log (Real.log (f k : ℝ)) := by
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let A : ℝ := B * Real.log 2
  have hA : 0 < A := mul_pos hB hl2
  let C : ℝ := 2 * Real.log 2 + |Real.log (Real.log 2)|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨r0, hr0⟩ := eventually_atTop.mp hsupply
  let t : ℕ → ℕ := fun k => ⌊(k : ℝ) / A⌋₊
  have htend : Tendsto t atTop atTop :=
    tendsto_nat_floor_atTop.comp
      (Tendsto.atTop_div_const hA (tendsto_natCast_atTop_atTop (R := ℝ)))
  have htevent : ∀ᶠ k : ℕ in atTop, r0 + 2 ≤ t k :=
    htend.eventually (eventually_ge_atTop (r0 + 2))
  have hkevent : ∀ᶠ k : ℕ in atTop, 2 * B * C ≤ (k : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (2 * B * C))
  filter_upwards [htevent, hkevent] with k htk hklarge
  let r : ℕ := 2 ^ t k
  have hr : r0 ≤ r := by
    have hpow : t k < 2 ^ t k := Nat.lt_two_pow_self
    dsimp [r]
    omega
  obtain ⟨ell, hell2, helllen, hellcount⟩ := hr0 r hr
  have htupper : (t k : ℝ) ≤ (k : ℝ) / A := Nat.floor_le (by positivity)
  have htupper' : (t k : ℝ) * A ≤ (k : ℝ) := (le_div_iff₀ hA).mp htupper
  have hellk : ell ≤ k := by
    have hlen : (ell : ℝ) ≤ B * ((t k : ℝ) * Real.log 2) := by
      simpa only [r, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using helllen
    have : (ell : ℝ) ≤ (k : ℝ) := by dsimp [A] at htupper'; nlinarith
    exact_mod_cast this
  have heq : 2 ^ (t k - 1) + 2 ^ (t k - 1) = 2 ^ t k := by
    have h := Nat.pow_sub_mul_pow 2 (by omega : 1 ≤ t k)
    norm_num at h
    omega
  have hexp : 2 ^ (t k - 1) ≤ r - 1 := by
    have hp : 1 ≤ 2 ^ (t k - 1) := Nat.one_le_pow _ _ (by decide)
    dsimp [r]
    omega
  have hcount : 2 ^ (2 ^ (t k - 1)) ≤ f k :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) hexp).trans
      (hellcount.trans (hmono ell k hell2 hellk))
  have hll := loglog_lower_of_two_pow_two_pow hcount
  rw [Nat.cast_sub (by omega : 1 ≤ t k), Nat.cast_one] at hll
  have htlower : (k : ℝ) / A < (t k : ℝ) + 1 := Nat.lt_floor_add_one _
  have htlower' : (k : ℝ) < ((t k : ℝ) + 1) * A := (div_lt_iff₀ hA).mp htlower
  have hquot : (k : ℝ) / B < ((t k : ℝ) + 1) * Real.log 2 := by
    apply (div_lt_iff₀ hB).2
    dsimp [A] at htlower'
    nlinarith
  have hlogabs : -|Real.log (Real.log 2)| ≤ Real.log (Real.log 2) := neg_abs_le _
  have hlower : (k : ℝ) / B - C ≤ Real.log (Real.log (f k : ℝ)) := by
    dsimp [C]
    linarith
  have hhalf : C ≤ (k : ℝ) / (2 * B) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * B)).2
    nlinarith [hklarge]
  have hdouble : (k : ℝ) / B = 2 * ((k : ℝ) / (2 * B)) := by
    field_simp
  have hresult : (k : ℝ) / (2 * B) ≤ Real.log (Real.log (f k : ℝ)) := by
    linarith
  simpa only [one_div, mul_comm, div_eq_mul_inv, one_mul] using hresult

end Problem337

end

end OAI
