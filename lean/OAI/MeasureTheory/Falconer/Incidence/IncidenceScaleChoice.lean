import OAI.MeasureTheory.Falconer.Incidence.CenteredPlanarIncidence

namespace OAI

/-! Choose a whole number of blocks at an arbitrary sufficiently small
original scale. Its ratio to the terminal grid is bounded independently of depth. -/
namespace Falconer

theorem incidence_block_scale_choice {B M : ℕ} (hB : 0 < B) {δ : ℝ} (hδ : 0 < δ)
    (hsmall : δ ≤ 1/(4*(2:ℝ)^(B*M))) :
    ∃ m : ℕ, M ≤ m ∧ 4*δ ≤ 1/(2:ℝ)^(m*B) ∧
      1/(2:ℝ)^(m*B) ≤ 4*(2:ℝ)^B*δ := by
  have hp : 1 < (2:ℝ)^B := one_lt_pow₀ (by norm_num) hB.ne'
  have hxM : ((2:ℝ)^B)^M ≤ 1/(4*δ) := by
    rw [← pow_mul]
    apply (le_div_iff₀ (by positivity : (0:ℝ) < 4*δ)).2
    have hh := (le_div_iff₀ (by positivity : (0:ℝ) < 4*(2:ℝ)^(B*M))).mp hsmall
    nlinarith only [hh]
  have hx1 : 1 ≤ 1/(4*δ) := (one_le_pow₀ hp.le).trans hxM
  obtain ⟨m,hmlo,hmhi⟩ := exists_nat_pow_near hx1 hp
  have hMm : M ≤ m := by
    by_contra h
    have hle : m+1 ≤ M := by omega
    have hh := pow_le_pow_right₀ hp.le hle
    exact (not_lt_of_ge (hh.trans hxM)) hmhi
  refine ⟨m,hMm,?_,?_⟩
  · rw [← pow_mul] at hmlo
    apply (le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^(m*B))).2
    have hh := (le_div_iff₀ (by positivity : (0:ℝ) < 4*δ)).mp hmlo
    simpa only [mul_comm,Nat.mul_comm] using hh
  · rw [pow_succ,← pow_mul] at hmhi
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^(m*B))).2
    have hh := (div_lt_iff₀ (by positivity : (0:ℝ) < 4*δ)).mp hmhi
    convert hh.le using 1
    simp only [Nat.mul_comm]
    ring

end Falconer

end OAI
