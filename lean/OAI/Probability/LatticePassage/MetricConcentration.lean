import OAI.Probability.LatticePassage.CenteredConcentration
import OAI.Probability.LatticePassage.CenteredLocalization

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real

lemma localization_shift_uniform (R : ℕ) :
    ((11/3 : ℝ)*R+4)*exp (-(log 2/40)*R) ≤ 300 := by
  have hlog := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hlog
  have hc : 1/80 ≤ log 2/40 := by linarith
  have hn : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
  have he : exp (-(log 2/40)*R) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
  have hb : (R : ℝ)/80 ≤ exp ((log 2/40)*R) := by
    have hp := mul_le_mul_of_nonneg_right hc hn
    linarith [add_one_le_exp ((log 2/40)*R)]
  have hm := mul_le_mul_of_nonneg_right hb (exp_pos (-(log 2/40)*R)).le
  have hid : exp ((log 2/40)*R)*exp (-(log 2/40)*R) = 1 := by
    rw [← exp_add]
    convert exp_zero using 2; ring
  rw [hid] at hm
  nlinarith

lemma sqrt_sixtyfour_mul (d : ℕ) : sqrt ((64*d : ℕ) : ℝ) = 8*sqrt d := by
  rw [Nat.cast_mul, Nat.cast_ofNat, sqrt_mul (by norm_num : (0 : ℝ) ≤ 64)]
  have he : sqrt (64 : ℝ) = 8 := by
    nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 64), sqrt_nonneg (64 : ℝ)]
  rw [he]

theorem passageTime_centered_intermediate (x y : Vertex) (hd : 1 ≤ latticeDistance x y)
    (t : ℝ) (ht : 600 ≤ t) (ht' : t ≤ 4*sqrt (latticeDistance x y)) :
    environmentLaw.real {ω | t*sqrt (latticeDistance x y) ≤
      |passageTime ω x y - ∫ η, passageTime η x y ∂environmentLaw|} ≤
      (2*exp 1+4)*exp (-t/64) := by
  let d := latticeDistance x y
  let R := 64*d
  have hR : 1 ≤ R := by dsimp [R,d]; omega
  have hscale : 40*latticeDistance x y ≤ R := by dsimp [R,d]; omega
  have hRd : latticeDistance x y < R := by dsimp [R,d]; omega
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ sqrt d := sqrt_nonneg _
  have hs1 : 1 ≤ sqrt d := by nlinarith [sq_sqrt (Nat.cast_nonneg d)]
  have hsd : sqrt d ≤ d := by nlinarith [sq_sqrt (Nat.cast_nonneg d)]
  have ht0 : 0 ≤ t := by linarith
  have hmean := localization_shift_uniform R
  have hthreshold : (t/16)*sqrt R ≤
      t*sqrt d - ((11/3 : ℝ)*R+4)*exp (-(log 2/40)*R) := by
    rw [show R = 64*d from rfl, sqrt_sixtyfour_mul]
    have hprod := mul_le_mul_of_nonneg_left hs1 ht0
    nlinarith
  have hlocal := localPassageTime_centered_exponential x y R hRd (t/16)
  have hlocal' := ENNReal.toReal_mono (by finiteness) hlocal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (exp_pos _).le] at hlocal'
  have hlog := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hlog
  have hdecay : exp (-(log 2/40)*R) ≤ exp (-t/64) := by
    apply exp_le_exp.mpr
    have hp := mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg d)
    dsimp [R]
    push_cast
    change t ≤ 4*sqrt d at ht'
    nlinarith
  apply (passageTime_centered_localization x y R hR hscale (t*sqrt d)).trans
  have hsub : environmentLaw.real {ω |
      t*sqrt d - ((11/3 : ℝ)*R+4)*exp (-(log 2/40)*R) ≤
        |localPassageTime ω x y R - ∫ η, localPassageTime η x y R ∂environmentLaw|} ≤
      environmentLaw.real {ω | (t/16)*sqrt R ≤
        |localPassageTime ω x y R - ∫ η, localPassageTime η x y R ∂environmentLaw|} :=
    measureReal_mono (fun _ h => hthreshold.trans h)
  calc
    _ ≤ (11/3 : ℝ)*exp (-t/64) + 2*exp (1-t/16/4) :=
      add_le_add (mul_le_mul_of_nonneg_left hdecay (by norm_num)) (hsub.trans hlocal')
    _ ≤ (2*exp 1+4)*exp (-t/64) := by
      rw [show 1-t/16/4 = 1+(-t/64) by ring, exp_add]
      nlinarith [exp_pos (-t/64)]

theorem passageTime_centered_concentration (x y : Vertex) (hd : 1 ≤ latticeDistance x y)
    (t : ℝ) (_ht : 0 ≤ t) :
    environmentLaw.real {ω | t*sqrt (latticeDistance x y) ≤
      |passageTime ω x y - ∫ η, passageTime η x y ∂environmentLaw|} ≤
      ((2*exp 1+4)*exp 10)*exp (-t/64) := by
  have hC : 1 ≤ 2*exp 1+4 := by linarith [exp_pos 1]
  have h10 : 1 ≤ exp (10 : ℝ) := one_le_exp_iff.mpr (by norm_num)
  by_cases hs : t ≤ 600
  · have hp : environmentLaw.real {ω | t*sqrt (latticeDistance x y) ≤
        |passageTime ω x y - ∫ η, passageTime η x y ∂environmentLaw|} ≤ 1 := by
      simp
    apply hp.trans
    rw [mul_assoc, ← exp_add]
    have he : 1 ≤ exp (10+-t/64) := one_le_exp_iff.mpr (by linarith)
    nlinarith
  · by_cases hl : 4*sqrt (latticeDistance x y) ≤ t
    · apply (passageTime_centered_large_sqrt x y hd t hl).trans
      have he : exp (-t/4) ≤ exp (-t/64) := exp_le_exp.mpr (by linarith)
      apply he.trans
      have hprod : (1 : ℝ) ≤ (2*exp 1+4)*exp 10 :=
        by simpa only [one_mul] using (mul_le_mul hC h10 (by norm_num) (by linarith))
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hprod (exp_pos (-t/64)).le
    · apply (passageTime_centered_intermediate x y hd t (by linarith) (by linarith)).trans
      have hnon : 0 ≤ (2*exp 1+4)*exp (-t/64) := by positivity
      have hprod := mul_le_mul_of_nonneg_left h10 hnon
      nlinarith [hprod]

theorem metric_centered_concentration :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ x y : Vertex, 2 ≤ latticeDistance x y →
      ∀ t : ℝ, 0 ≤ t → environmentLaw.real {ω |
        t*sqrt (latticeDistance x y) ≤
          |passageTime ω x y - ∫ η, passageTime η x y ∂environmentLaw|} ≤ C*exp (-c*t) := by
  refine ⟨(2*exp 1+4)*exp 10, 1/64, by positivity, by norm_num, ?_⟩
  intro x y hd t ht
  simpa only [show -(1/64 : ℝ)*t = -t/64 by ring] using
    passageTime_centered_concentration x y (by omega) t ht

end CompanionFPP

end OAI
