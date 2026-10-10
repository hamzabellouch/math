import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.EulerTrajectory

namespace OAI

/-! Polynomial step count, sample precision, and register denominator for
unit-time integration with fixed speed/Lipschitz guards. The same step
count is used as the velocity sample precision. -/

namespace ContinuumCoulomb.EulerRegisters

def steps (C P : ℕ) : ℕ := 16*C^2*(P+1)
def denominator (C P : ℕ) : ℕ := (steps C P)^2

theorem steps_positive {C P : ℕ} (hC : 0 < C) : 0 < steps C P := by
  unfold steps
  positivity

theorem schedule_budget {C P : ℕ} (hC : 0 < C) {L M : ℝ}
    (hExp : Real.exp L ≤ (C:ℝ)) (hLM : L*(1+M) ≤ C) :
    (3/(denominator C P:ℝ)+((steps C P:ℝ)+1)⁻¹+
      L*(1+M)/(steps C P:ℝ)+3*(steps C P:ℝ)/(denominator C P:ℝ))*Real.exp L ≤
      ((P:ℝ)+1)⁻¹ := by
  let N : ℝ := steps C P
  have hCp : (0:ℝ) < C := by exact_mod_cast hC
  have hC1 : (1:ℝ) ≤ C := by exact_mod_cast hC
  have hNp : 0 < N := by dsimp [N]; exact_mod_cast steps_positive (P := P) hC
  have hN1 : 1 ≤ N := by dsimp [N]; exact_mod_cast steps_positive (P := P) hC
  have hN : N = 16*(C:ℝ)^2*((P:ℝ)+1) := by
    simp only [N,steps,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
  have hD : (denominator C P:ℝ) = N^2 := by simp only [denominator,Nat.cast_pow,N]
  have hq : 0 < (P:ℝ)+1 := by positivity
  have hi : 3/(denominator C P:ℝ) ≤ 3/N := by
    rw [hD]
    apply (div_le_div_iff₀ (sq_pos_of_pos hNp) hNp).mpr
    nlinarith
  have hs : ((steps C P:ℝ)+1)⁻¹ ≤ 1/N := by
    change (N+1)⁻¹ ≤ 1/N
    rw [one_div]
    exact inv_anti₀ hNp (le_add_of_nonneg_right zero_le_one)
  have hl : L*(1+M)/(steps C P:ℝ) ≤ (C:ℝ)/N :=
    div_le_div_of_nonneg_right hLM hNp.le
  have hr : 3*(steps C P:ℝ)/(denominator C P:ℝ) = 3/N := by
    rw [hD]
    change 3*N/N^2 = 3/N
    field_simp [hNp.ne']
  have ht : 3/(denominator C P:ℝ)+((steps C P:ℝ)+1)⁻¹+
      L*(1+M)/(steps C P:ℝ)+3*(steps C P:ℝ)/(denominator C P:ℝ) ≤ 8*(C:ℝ)/N := by
    rw [hr]
    have hc : 3/N+1/N+(C:ℝ)/N+3/N ≤ 8*(C:ℝ)/N := by
      calc
        _ = ((C:ℝ)+7)/N := by ring
        _ ≤ 8*(C:ℝ)/N := div_le_div_of_nonneg_right (by nlinarith) hNp.le
    exact (add_le_add (add_le_add (add_le_add hi hs) hl) le_rfl).trans hc
  calc
    _ ≤ (8*(C:ℝ)/N)*Real.exp L := mul_le_mul_of_nonneg_right ht (Real.exp_pos L).le
    _ ≤ (8*(C:ℝ)/N)*(C:ℝ) := mul_le_mul_of_nonneg_left hExp (by positivity)
    _ = (1/2:ℝ)*((P:ℝ)+1)⁻¹ := by
      rw [hN]
      field_simp [hCp.ne',hq.ne']
      norm_num
    _ ≤ ((P:ℝ)+1)⁻¹ := mul_le_of_le_one_left (inv_nonneg.mpr hq.le) (by norm_num)

end ContinuumCoulomb.EulerRegisters

end OAI
