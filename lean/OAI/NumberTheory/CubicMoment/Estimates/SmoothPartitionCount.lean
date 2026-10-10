import OAI.NumberTheory.CubicMoment.Estimates.SmoothTuplePartition

namespace OAI

/-! A concrete truncation and subpower cost for the smooth norm partition. -/
noncomputable section
namespace CubicFirstMoment

def normPartitionCount (B : ℝ) : ℕ :=
  ⌈Real.log (2*B)/Real.log (4/3:ℝ)⌉₊

lemma normPartitionCount_covers {B : ℝ} (hB : 1 ≤ B) :
    2*B ≤ (4/3:ℝ)^normPartitionCount B := by
  have hr : 0 < Real.log (4/3:ℝ) := Real.log_pos (by norm_num)
  apply (Real.log_le_log_iff (by linarith : 0 < 2*B)
    (pow_pos (by norm_num : (0:ℝ) < 4/3) _)).mp
  rw [Real.log_pow]
  exact (div_le_iff₀ hr).mp (Nat.le_ceil _)

theorem normPartitionCount_log_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ B : ℝ, 1 ≤ B →
      (normPartitionCount B : ℝ) ≤ K*(1+Real.log B) := by
  let r := Real.log (4/3:ℝ)
  have hr : 0 < r := Real.log_pos (by norm_num)
  let a := 1+Real.log 2/r
  let b := 1/r
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  refine ⟨a+b,by linarith,?_⟩
  intro B hB
  have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
  have hn := (Nat.ceil_lt_add_one
    (div_nonneg (Real.log_nonneg (by linarith : 1 ≤ 2*B)) hr.le)).le
  change (normPartitionCount B : ℝ) ≤ _ at hn
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by linarith : B ≠ 0),add_div] at hn
  have he : Real.log 2/r+Real.log B/r+1 = a+b*Real.log B := by dsimp [a,b]; ring
  apply hn.trans
  rw [he]
  nlinarith [mul_nonneg ha hlog]

theorem normPartitionCount_power_bound (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 1 ≤ B →
      (normPartitionCount B : ℝ)^d ≤ C*B^ε := by
  obtain ⟨K,hK,hcount⟩ := normPartitionCount_log_bound
  have hd : 0 < (d:ℝ)+1 := by positivity
  obtain ⟨A,hA,hlog⟩ := one_add_log_small_power (div_pos hε hd)
  refine ⟨(K*A)^d,pow_pos (mul_pos hK hA) _,?_⟩
  intro B hB
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hnb : (normPartitionCount B : ℝ) ≤ (K*A)*B^(ε/((d:ℝ)+1)) :=
    (hcount B hB).trans (by
      calc
        K*(1+Real.log B) ≤ K*(A*B^(ε/((d:ℝ)+1))) :=
          mul_le_mul_of_nonneg_left (hlog B hB) hK.le
        _ = _ := by ring)
  have he : ε/((d:ℝ)+1)*(d:ℝ) ≤ ε := by
    have hm := div_mul_cancel₀ ε hd.ne'
    have hp : 0 < ε/((d:ℝ)+1) := div_pos hε hd
    nlinarith
  calc
    _ ≤ ((K*A)*B^(ε/((d:ℝ)+1)))^d :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hnb d
    _ = (K*A)^d*B^(ε/((d:ℝ)+1)*(d:ℝ)) := by
      rw [mul_pow,← Real.rpow_mul_natCast hBp.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hB he) (pow_nonneg (mul_pos hK hA).le _)

end CubicFirstMoment

end

end OAI
