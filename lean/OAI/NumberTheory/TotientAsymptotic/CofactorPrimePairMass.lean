import OAI.NumberTheory.TotientAsymptotic.UniformPrimePairBound
import OAI.NumberTheory.TotientAsymptotic.TotientRatioLogLog

namespace OAI

/-! Summing the uniform prime-pair sieve over a specified cofactor family. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma cofactor_prime_pair_mass : ∃ C : ℝ, 0 < C ∧ ∀ x L : ℝ,
    Real.exp 2 ≤ x → 0 < L → ∀ Q : Finset ℕ,
    (∀ b ∈ Q,0 < b ∧ (b:ℝ) ≤ x ∧ 2 ≤ ⌊x/b⌋₊ ∧ L ≤ Real.log (⌊x/b⌋₊:ℝ)) →
    (∑ b ∈ Q,((allShiftedPrimePairs b ⌊x/b⌋₊).card:ℝ)) ≤
      C*x*B x/L^2*(∑ b ∈ Q,(b:ℝ)⁻¹) := by
  obtain ⟨C,hC,hpair⟩ := uniform_prime_pair_bound
  obtain ⟨D,hD,hratio⟩ := totient_ratio_loglog_bound
  refine ⟨C*D,by positivity,?_⟩
  intro x L hx hL Q hQ
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have hlogx : 2 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have hB : 0 ≤ B x := Real.log_nonneg (by linarith)
  have hterm (b : ℕ) (hb : b ∈ Q) :
      ((allShiftedPrimePairs b ⌊x/b⌋₊).card:ℝ) ≤ C*D*x*B x/L^2*(b:ℝ)⁻¹ := by
    obtain ⟨hb0,hbx,hX,hXL⟩ := hQ b hb
    have hbR : (0:ℝ) < b := by exact_mod_cast hb0
    have hfloor : (⌊x/b⌋₊:ℝ) ≤ x/b := Nat.floor_le (div_nonneg hx0.le hbR.le)
    have hrat : (b:ℝ)/b.totient ≤ D*B x := hratio x hx b hb0 hbx
    have hrat0 : 0 ≤ (b:ℝ)/b.totient := by positivity
    have hlogX : 0 < Real.log (⌊x/b⌋₊:ℝ) := hL.trans_le hXL
    calc
      _ ≤ C*(⌊x/b⌋₊:ℝ)*((b:ℝ)/b.totient)/(Real.log (⌊x/b⌋₊:ℝ))^2 :=
        hpair b hb0 _ hX
      _ ≤ C*(x/b)*(D*B x)/L^2 := by
        apply div_le_div₀
        · positivity
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hfloor hC.le) hrat hrat0
            (by positivity)
        · exact sq_pos_of_pos hL
        · exact pow_le_pow_left₀ hL.le hXL 2
      _ = _ := by ring
  calc
    _ ≤ ∑ b ∈ Q,C*D*x*B x/L^2*(b:ℝ)⁻¹ := Finset.sum_le_sum hterm
    _ = _ := (Finset.mul_sum ..).symm

end TotientAsymptotic

end

end OAI
