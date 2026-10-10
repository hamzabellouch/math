import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibratedBisectionSchedule

namespace OAI

/-! A rational approximation to the logarithmic contact scale. Only a fixed
rational approximation to `log 2` is used. The input-dependent operation is
the bit length of a natural power, so no real logarithm is queried at runtime. -/

noncomputable section
namespace ContinuumCoulomb.RationalLogScale

def value (c : ℚ) (k N : ℕ) : ℚ := c * ((N ^ k).bits.length : ℚ)

theorem bitLength_log_error (m : ℕ) (hm : 0 < m) :
    0 ≤ ((m.bits.length : ℝ) * Real.log 2 - Real.log (m : ℝ)) ∧
      (m.bits.length : ℝ) * Real.log 2 - Real.log (m : ℝ) ≤ Real.log 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 < m.size := Nat.size_pos.mpr hm
  obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  have hlo : 2 ^ s ≤ m := Nat.lt_size.mp (by omega)
  have hhi : m < 2 ^ (s + 1) := by simpa only [hs] using Nat.lt_size_self m
  have hloR : (2 : ℝ) ^ s ≤ m := by exact_mod_cast hlo
  have hhiR : (m : ℝ) < 2 ^ (s + 1) := by exact_mod_cast hhi
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ s) hloR
  have hh := Real.log_lt_log hmR hhiR
  rw [Real.log_pow] at hl hh
  simp only [Nat.size_eq_bits_len, hs, Nat.cast_succ] at *
  constructor <;> nlinarith

theorem exists_logTwo_approximation {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ c : ℚ, 0 < c ∧ |(c : ℝ) - Real.log 2| ≤ ε / 4 * Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨c, hc0, hc1⟩ := exists_rat_btwn
    (show (1 - ε / 4) * Real.log 2 < (1 + ε / 4) * Real.log 2 by
      nlinarith [mul_pos hε hlog])
  refine ⟨c, ?_, abs_le.mpr ⟨?_, ?_⟩⟩
  · have : (0 : ℝ) < c := (mul_pos (by linarith : 0 < 1 - ε / 4) hlog).trans hc0
    exact_mod_cast this
  · nlinarith
  · nlinarith

theorem relative_error (c : ℚ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hc : |(c : ℝ) - Real.log 2| ≤ ε / 4 * Real.log 2)
    (k N : ℕ) (hN : 2 ≤ N) (hk : 8 ≤ ε * (k : ℝ)) :
    |(value c k N : ℝ) - (k : ℝ) * Real.log (N : ℝ)| ≤
      ε * ((k : ℝ) * Real.log (N : ℝ)) := by
  have hNp : 0 < N := by omega
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : Real.log 2 ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hE0 : 0 ≤ (k : ℝ) * Real.log (N : ℝ) := mul_nonneg (Nat.cast_nonneg _) (hlog.le.trans hlogN)
  obtain ⟨hb0, hb1⟩ := bitLength_log_error (N ^ k) (pow_pos hNp k)
  rw [Nat.cast_pow, Real.log_pow] at hb0 hb1
  have htriangle := abs_add_le
    (((N ^ k).bits.length : ℝ) * ((c : ℝ) - Real.log 2))
    (((N ^ k).bits.length : ℝ) * Real.log 2 - (k : ℝ) * Real.log (N : ℝ))
  have hchange : |(value c k N : ℝ) - (k : ℝ) * Real.log (N : ℝ)| ≤
      (((N ^ k).bits.length : ℝ) * (ε / 4 * Real.log 2)) + Real.log 2 := by
    have hmul := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (N ^ k).bits.length :
      (0 : ℝ) ≤ (N ^ k).bits.length)
    have habs : |((N ^ k).bits.length : ℝ) * ((c : ℝ) - Real.log 2)| ≤
        ((N ^ k).bits.length : ℝ) * (ε / 4 * Real.log 2) := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact hmul
    rw [show |((N ^ k).bits.length : ℝ) * Real.log 2 -
        (k : ℝ) * Real.log (N : ℝ)| =
        ((N ^ k).bits.length : ℝ) * Real.log 2 - (k : ℝ) * Real.log (N : ℝ)
      from abs_of_nonneg hb0] at htriangle
    have heq : (value c k N : ℝ) - (k : ℝ) * Real.log (N : ℝ) =
        ((N ^ k).bits.length : ℝ) * ((c : ℝ) - Real.log 2) +
          (((N ^ k).bits.length : ℝ) * Real.log 2 - (k : ℝ) * Real.log (N : ℝ)) := by
      simp only [value, Rat.cast_mul, Rat.cast_natCast]
      ring
    rw [heq]
    exact htriangle.trans (add_le_add habs hb1)
  have hround : 2 * Real.log 2 ≤ ε / 4 * ((k : ℝ) * Real.log (N : ℝ)) := by
    have hcount : (2 : ℝ) ≤ ε / 4 * (k : ℝ) := by nlinarith
    have h₁ := mul_le_mul_of_nonneg_right hcount hlog.le
    have h₂ := mul_le_mul_of_nonneg_left hlogN
      (show 0 ≤ ε / 4 * (k : ℝ) by positivity)
    nlinarith only [h₁, h₂]
  have hbit := mul_le_mul_of_nonneg_left hb1 (show 0 ≤ ε / 4 by positivity)
  have hsmall : ε / 4 * Real.log 2 ≤ Real.log 2 :=
    (mul_le_mul_of_nonneg_right (by linarith : ε / 4 ≤ 1) hlog.le).trans_eq (one_mul _)
  have hscaled := mul_nonneg hε.le hE0
  nlinarith only [hchange, hbit, hsmall, hround, hscaled]

theorem relative_bounds (c : ℚ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hc : |(c : ℝ) - Real.log 2| ≤ ε / 4 * Real.log 2)
    (k N : ℕ) (hN : 2 ≤ N) (hk : 8 ≤ ε * (k : ℝ)) :
    (1 - ε) * ((k : ℝ) * Real.log (N : ℝ)) ≤ (value c k N : ℝ) ∧
      (value c k N : ℝ) ≤ (1 + ε) * ((k : ℝ) * Real.log (N : ℝ)) := by
  have h := abs_le.mp (relative_error c hε hε1 hc k N hN hk)
  constructor <;> nlinarith [h.1, h.2]

end ContinuumCoulomb.RationalLogScale

end

end OAI
