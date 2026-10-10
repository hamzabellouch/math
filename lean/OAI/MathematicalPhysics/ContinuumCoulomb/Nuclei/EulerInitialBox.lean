import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.EulerSchedule

namespace OAI

/-! A binary-encoded box radius computed directly from the three input
rational numerators encloses the true bounded-speed trajectory. -/

noncomputable section
namespace ContinuumCoulomb.EulerRegisters
open CappedKernelProgram (Triple position)

def inputRadius (q : Triple) : ℕ := q.1.num.natAbs+q.2.1.num.natAbs+q.2.2.num.natAbs

def boxNumerator (C D : ℕ) (q : Triple) : ℕ := D*(inputRadius q+C+1)

private theorem rational_abs_le_num (q : ℚ) : |(q:ℝ)| ≤ (q.num.natAbs:ℝ) := by
  have hd : (1:ℝ) ≤ q.den := by exact_mod_cast (Nat.succ_le_of_lt q.pos)
  have hp : (0:ℝ) < q.den := by exact_mod_cast q.pos
  rw [Rat.cast_def,abs_div,abs_of_pos hp,Nat.cast_natAbs,Int.cast_abs]
  exact (div_le_self (abs_nonneg _) hd)

theorem inputRadius_bound (q : Triple) (a : Fin 3) : |position q a| ≤ (inputRadius q:ℝ) := by
  have h0 := rational_abs_le_num q.1
  have h1 := rational_abs_le_num q.2.1
  have h2 := rational_abs_le_num q.2.2
  have hn0 : (0:ℝ) ≤ q.1.num.natAbs := Nat.cast_nonneg _
  have hn1 : (0:ℝ) ≤ q.2.1.num.natAbs := Nat.cast_nonneg _
  have hn2 : (0:ℝ) ≤ q.2.2.num.natAbs := Nat.cast_nonneg _
  simp only [Nat.cast_natAbs,Int.cast_abs] at h0 h1 h2 hn0 hn1 hn2
  fin_cases a <;> simp only [inputRadius,Nat.cast_add,position,PiLp.toLp_apply] <;> norm_num <;> linarith

theorem boxNumerator_ratio {D C : ℕ} (hD : 0 < D) (q : Triple) :
    (boxNumerator C D q:ℝ)/(D:ℝ) = (inputRadius q:ℝ)+(C:ℝ)+1 := by
  have hd : (D:ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  simp only [boxNumerator,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  field_simp

theorem initial_round_error {D C : ℕ} (hD : 0 < D) (q : Triple) :
    ‖position (point D (round D (boxNumerator C D q) q))-position q‖ ≤ 3/(D:ℝ) := by
  have h := round_position_error (B := boxNumerator C D q) hD q (position q) (fun a => by
    rw [boxNumerator_ratio (C := C) hD]
    exact (inputRadius_bound q a).trans (by linarith [Nat.cast_nonneg (α := ℝ) C]))
  simpa only [sub_self,norm_zero,zero_add] using h

end ContinuumCoulomb.EulerRegisters

end

end OAI
