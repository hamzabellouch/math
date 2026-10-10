import OAI.NumberTheory.TotientAsymptotic.CountingEnvelopeReal

namespace OAI

/-! Reciprocal mass of all totient values below a finite endpoint. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem bounded_totient_reciprocal_mass : ∃ C : ℝ,0 < C ∧ ∀ U : ℝ,4 ≤ U → 1 ≤ B U →
    ∀ Q : Finset ℕ,(∀ v ∈ Q,IsTotient v ∧ (v:ℝ) ≤ U) →
    (∑ v ∈ Q,(v:ℝ)⁻¹) ≤ C*Real.exp (10*(Real.log (B U+4))^2) := by
  obtain ⟨C,hC,henv⟩ := counting_envelope_real_bound
  refine ⟨1+4*C,by positivity,?_⟩
  intro U hU hBU Q hQ
  have hi := counting_dyadic_index_bounds hU
  let J := countingDyadicIndex U
  have hm := dyadic_totient_reciprocal_mass hi.1 Q (by
    intro v hv
    exact ⟨(hQ v hv).1,(hQ v hv).2.trans hi.2.1⟩)
  have hJ1 : (1:ℝ) ≤ J := by exact_mod_cast hi.1
  have hJ0 : (0:ℝ) < J := by linarith only [hJ1]
  have hlog0 : 0 ≤ 1+Real.log J := by linarith [Real.log_nonneg hJ1]
  have hlog : 1+Real.log J ≤ B U+4 := by
    have hh := Real.log_le_log hJ0 (show (J:ℝ) ≤ (J:ℝ)+1 by linarith)
    have ht := hi.2.2
    change 1+Real.log ((J:ℝ)+1) ≤ B U+4 at ht
    linarith only [hh,ht]
  have henvU := henv U hU
  have hp := mul_le_mul henvU hlog hlog0 (by positivity)
  have hbase : 0 < B U+4 := by linarith only [hBU]
  have hl : 1 ≤ Real.log (B U+4) := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<3) (show (3:ℝ) ≤ B U+4 by linarith)
    linarith [Real.log_three_gt_d9]
  have hgrow : Real.exp (9*(Real.log (B U+4))^2)*(B U+4) ≤
      Real.exp (10*(Real.log (B U+4))^2) := by
    calc
      _ = Real.exp (9*(Real.log (B U+4))^2+Real.log (B U+4)) := by
        rw [Real.exp_add,Real.exp_log hbase]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [hl])
  have hone : 1 ≤ Real.exp (10*(Real.log (B U+4))^2) := Real.one_le_exp (by positivity)
  have hh := mul_le_mul_of_nonneg_left hgrow hC.le
  nlinarith only [hm,hp,hh,hone]

end TotientAsymptotic

end

end OAI
