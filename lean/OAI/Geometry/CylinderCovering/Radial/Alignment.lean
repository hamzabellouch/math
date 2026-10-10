import Mathlib

namespace OAI

open Set MeasureTheory
open scoped Interval

namespace RadialAlignment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem alignment_integral
    {α β c t : ℝ} {a b : E} {w : ℝ → E} {lam : ℝ → ℝ}
    (hlam : ContinuousOn lam (Icc α β))
    (hw : ContinuousOn w (Icc α β))
    (hder : ∀ x ∈ Ioo α β, HasDerivAt w (lam x • (a + x • b)) x)
    (hc : c ∈ Icc α β) (ht : t ∈ Icc α β) :
    w t - w c = (∫ x in c..t, lam x) • a +
      (∫ x in c..t, lam x * x) • b := by
  have hsub : uIcc c t ⊆ Icc α β := uIcc_subset_Icc hc ht
  have hl : ContinuousOn lam (uIcc c t) := hlam.mono hsub
  have hlin : ContinuousOn (fun x : ℝ => a + x • b) (uIcc c t) :=
    continuousOn_const.add (continuousOn_id.smul continuousOn_const)
  have hFTC : (∫ x in c..t, lam x • (a + x • b)) = w t - w c := by
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right (hw.mono hsub)
    · intro x hx
      have hinner : x ∈ Ioo α β := by
        constructor
        · exact lt_of_le_of_lt (le_min hc.1 ht.1) hx.1
        · exact lt_of_lt_of_le hx.2 (max_le hc.2 ht.2)
      exact (hder x hinner).hasDerivWithinAt
    · exact (hl.smul hlin).intervalIntegrable
  rw [← hFTC]
  have ha : IntervalIntegrable (fun x => lam x • a) volume c t :=
    (hl.smul continuousOn_const).intervalIntegrable
  have hb : IntervalIntegrable (fun x => (lam x * x) • b) volume c t :=
    ((hl.mul continuousOn_id).smul continuousOn_const).intervalIntegrable
  simp_rw [smul_add, smul_smul]
  rw [intervalIntegral.integral_add ha hb]
  simp only [intervalIntegral.integral_smul_const]

theorem centered_integral
    {α β c t : ℝ} {lam : ℝ → ℝ}
    (hlam : ContinuousOn lam (Icc α β))
    (hc : c ∈ Icc α β) (ht : t ∈ Icc α β) :
    (∫ x in c..t, lam x * (x - t)) =
      (∫ x in c..t, lam x * x) - t * (∫ x in c..t, lam x) := by
  have hl : ContinuousOn lam (uIcc c t) := hlam.mono (uIcc_subset_Icc hc ht)
  have h₁ : IntervalIntegrable (fun x => lam x * x) volume c t :=
    (hl.mul continuousOn_id).intervalIntegrable
  have h₂ : IntervalIntegrable (fun x => t * lam x) volume c t :=
    (continuousOn_const.mul hl).intervalIntegrable
  simp_rw [mul_sub, mul_comm (lam _) t]
  rw [intervalIntegral.integral_sub h₁ h₂, intervalIntegral.integral_const_mul]

theorem frozen_intercept
    {α β c t ρ s : ℝ} {p₀ e a b : E} {w : ℝ → E} {lam : ℝ → ℝ}
    (hlam : ContinuousOn lam (Icc α β))
    (hw : ContinuousOn w (Icc α β))
    (hder : ∀ x ∈ Ioo α β, HasDerivAt w (lam x • (a + x • b)) x)
    (hc : c ∈ Icc α β) (ht : t ∈ Icc α β) :
    let u := ρ + s * (∫ x in c..t, lam x)
    let v := t * u + s * (∫ x in c..t, lam x * (x - t))
    p₀ + ρ • (a + t • b) + s • (e + w t) - s • (e + w c) =
      p₀ + u • a + v • b := by
  dsimp only
  have hvec := alignment_integral hlam hw hder hc ht
  have hcenter := centered_integral hlam hc ht
  rw [hcenter]
  have hwt : w t = w c +
      ((∫ x in c..t, lam x) • a + (∫ x in c..t, lam x * x) • b) := by
    rw [← hvec]
    abel
  rw [hwt]
  module

end RadialAlignment

end OAI
