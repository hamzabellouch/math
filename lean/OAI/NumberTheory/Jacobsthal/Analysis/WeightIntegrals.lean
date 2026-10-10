import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic
import OAI.NumberTheory.Jacobsthal.Paths.FiniteHistorySupport

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.TwoStepDensityBounds

open Set
open DerivativeWeights WeightFutureIntegrals FinitePathGeometry

noncomputable def baseRatio : Side → ℝ | .even => 198 / 100 | .odd => 95 / 100

theorem baseRatio_valid (i : Side) : Valid i (baseRatio i) := by cases i <;> exact le_rfl

theorem baseRatio_le {i : Side} {s : ℝ} (hs : Valid i s) : baseRatio i ≤ s := by
  cases i <;> exact hs

theorem valid_of_three_le (i : Side) {s : ℝ} (hs : 3 ≤ s) : Valid i s := by
  cases i <;> dsimp [Valid] <;> linarith

theorem weight_antitone {i : Side} {s t : ℝ} (hs : Valid i s) (ht : Valid i t) (hst : s ≤ t) :
    weight i t ≤ weight i s := by
  cases i with
  | even =>
    exact phiEven_strictAntiOn.antitoneOn
      (by change 1 < s; dsimp [Valid] at hs; linarith)
      (by change 1 < t; dsimp [Valid] at ht; linarith) hst
  | odd => exact phiOdd_antitone hst

theorem two_step_density_eq {i : Side} {s t u : ℝ} (hs : Valid i s)
    (ht : minRatio i s ≤ t) (hu : minRatio i.flip t ≤ u) :
    transitionDensity i s t * transitionDensity i.flip t u =
      (W t * W u) * (weight i u / weight i s) := by
  have htV := valid_next hs ht
  have hw := weight_pos hs
  have hwt := weight_pos htV
  have hflip : i.flip.flip = i := by cases i <;> rfl
  unfold transitionDensity TransitionKernels.tailDensity
  rw [indicator_of_mem (show t ∈ Ici (minRatio i s) from ht),
    indicator_of_mem (show u ∈ Ici (minRatio i.flip t) from hu), hflip]
  field_simp

theorem rectangle_admissible {i : Side} {s L t u : ℝ} (hL : 3 ≤ L) (hsL : s ≤ L)
    (ht : t ∈ Icc L (L + 1)) (hu : u ∈ Icc (L + 1) (L + 2)) :
    minRatio i s ≤ t ∧ minRatio i.flip t ≤ u := by
  cases i <;> dsimp [minRatio, Side.flip]
  · constructor
    · linarith [ht.1]
    · apply max_le <;> linarith [ht.2, hu.1]
  · constructor
    · apply max_le <;> linarith [ht.1]
    · linarith [ht.2, hu.1]

theorem W_lower {t M : ℝ} (ht : 0 < t) (htM : t ≤ M) : 1 / M ≤ W t := by
  have hM : 0 < M := lt_of_lt_of_le ht htM
  unfold W
  apply (div_le_div_iff₀ hM (sq_pos_of_pos ht)).mpr
  nlinarith

noncomputable def rectangleLower (i : Side) (L : ℝ) : ℝ :=
  (1 / (L + 2)) ^ 2 * (weight i (L + 2) / weight i (baseRatio i))

theorem rectangleLower_pos (i : Side) {L : ℝ} (hL : 3 ≤ L) : 0 < rectangleLower i L := by
  unfold rectangleLower
  exact mul_pos (sq_pos_of_pos (one_div_pos.mpr (by linarith)))
    (div_pos (weight_pos (valid_of_three_le i (by linarith))) (weight_pos (baseRatio_valid i)))

theorem rectangle_density_lower {i : Side} {s L t u : ℝ} (hL : 3 ≤ L)
    (hs : Valid i s) (hsL : s ≤ L)
    (ht : t ∈ Icc L (L + 1)) (hu : u ∈ Icc (L + 1) (L + 2)) :
    rectangleLower i L ≤ transitionDensity i s t * transitionDensity i.flip t u := by
  obtain ⟨hadt, hadu⟩ := rectangle_admissible (i := i) hL hsL ht hu
  rw [two_step_density_eq hs hadt hadu]
  have ht0 : 0 < t := by linarith [ht.1]
  have hu0 : 0 < u := by linarith [hu.1]
  have htM : t ≤ L + 2 := by linarith [ht.2]
  have hW : (1 / (L + 2)) ^ 2 ≤ W t * W u := by
    simpa only [pow_two] using mul_le_mul (W_lower ht0 htM) (W_lower hu0 hu.2)
      (one_div_nonneg.mpr (by linarith)) (W_pos ht0).le
  have hsW := weight_pos hs
  have hbaseW := weight_pos (baseRatio_valid i)
  have hMW := weight_pos (valid_of_three_le i (s := L + 2) (by linarith))
  have huV := valid_of_three_le i (s := u) (by linarith [hu.1])
  have hden := weight_antitone (baseRatio_valid i) hs (baseRatio_le hs)
  have hnum := weight_antitone huV (valid_of_three_le i (s := L + 2) (by linarith)) hu.2
  have hratio : weight i (L + 2) / weight i (baseRatio i) ≤ weight i u / weight i s := by
    calc
      _ ≤ weight i (L + 2) / weight i s := div_le_div_of_nonneg_left hMW.le hsW hden
      _ ≤ _ := div_le_div_of_nonneg_right hnum hsW.le
  exact mul_le_mul hW hratio (div_pos hMW hbaseW).le (mul_pos (W_pos ht0) (W_pos hu0)).le

noncomputable def minorizationSize (L : ℝ) : ℝ :=
  min 1 (min (rectangleLower .even L) (rectangleLower .odd L))

theorem minorizationSize_pos {L : ℝ} (hL : 3 ≤ L) : 0 < minorizationSize L :=
  lt_min zero_lt_one (lt_min (rectangleLower_pos .even hL) (rectangleLower_pos .odd hL))

theorem minorizationSize_le_one (L : ℝ) : minorizationSize L ≤ 1 := min_le_left _ _

theorem minorizationSize_le_rectangle (i : Side) (L : ℝ) : minorizationSize L ≤ rectangleLower i L := by
  cases i with
  | even => exact le_trans (min_le_right _ _) (min_le_left _ _)
  | odd => exact le_trans (min_le_right _ _) (min_le_right _ _)

end NumberTheoryLean.TwoStepDensityBounds

end

section

open Set MeasureTheory
namespace Erdos970Dependency.WeightIntegrals
open NumberTheoryLean.DerivativeWeights NumberTheoryLean.WeightFutureIntegrals

noncomputable def wPrimitive (t : ℝ) : ℝ := Real.log t - 1 / t
noncomputable def wMass (a b : ℝ) : ℝ := ∫ t in a..b, W t

theorem W_continuousAt {t : ℝ} (ht : t ≠ 0) : ContinuousAt W t := by
  unfold W
  fun_prop (disch := simp [ht])

theorem wPrimitive_deriv {t : ℝ} (ht : 0 < t) : HasDerivAt wPrimitive (W t) t := by
  have h := (Real.hasDerivAt_log (ne_of_gt ht)).sub
    ((hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) (ne_of_gt ht))
  convert! h using 1
  simp only [W, id_eq, zero_mul, zero_sub, mul_one]
  field_simp
  ring

theorem wMass_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    wMass a b = wPrimitive b - wPrimitive a := by
  have hp (t : ℝ) (ht : t ∈ uIcc a b) : 0 < t :=
    lt_of_lt_of_le (lt_min ha hb) ht.1
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    exact wPrimitive_deriv (hp t ht)
  · apply ContinuousOn.intervalIntegrable
    intro t ht
    exact (W_continuousAt (ne_of_gt (hp t ht))).continuousWithinAt

theorem wMass_nonneg {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : 0 ≤ wMass a b := by
  apply intervalIntegral.integral_nonneg hab
  intro t ht
  exact (W_pos (ha.trans_le ht.1)).le

theorem wMass_mono_right {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) :
    wMass a b ≤ wMass a c := by
  have hsplit : wMass a c = wMass a b + wMass b c := by
    rw [wMass_eq ha (ha.trans_le (hab.trans hbc)), wMass_eq ha (ha.trans_le hab),
      wMass_eq (ha.trans_le hab) (ha.trans_le (hab.trans hbc))]
    ring
  rw [hsplit]
  linarith [wMass_nonneg (ha.trans_le hab) hbc]

theorem wMass_two_three_lower : (1 : ℝ) / 3 ≤ wMass 2 3 := by
  have hW : ∀ t ∈ Icc (2 : ℝ) 3, (1 : ℝ) / 3 ≤ W t := by
    intro t ht
    exact NumberTheoryLean.TwoStepDensityBounds.W_lower (by linarith [ht.1]) ht.2
  have hI : IntervalIntegrable W volume 2 3 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] at ht
    exact (W_continuousAt (by linarith [ht.1])).continuousWithinAt
  have h := intervalIntegral.integral_mono_on (by norm_num : (2 : ℝ) ≤ 3)
    (by simp : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ) / 3) volume 2 3) hI hW
  norm_num only [intervalIntegral.integral_const, smul_eq_mul] at h
  exact h

theorem wMass_initial_upper {a : ℝ} (ha : 99 / 100 ≤ a) (ha2 : a ≤ 2) : wMass a 2 ≤ 5 := by
  have ha0 : 0 < a := by linarith
  have hW : ∀ t ∈ Icc a (2 : ℝ), W t ≤ 4 := by
    intro t ht
    have ht0 : 0 < t := ha0.trans_le ht.1
    unfold W
    apply (div_le_iff₀ (sq_pos_of_pos ht0)).mpr
    nlinarith [sq_nonneg (t - 99 / 100), ht.1, ht.2]
  have hI : IntervalIntegrable W volume a 2 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le ha2] at ht
    exact (W_continuousAt (ne_of_gt (ha0.trans_le ht.1))).continuousWithinAt
  have h := intervalIntegral.integral_mono_on ha2 hI
    (by simp : IntervalIntegrable (fun _ : ℝ ↦ (4 : ℝ)) volume a 2) hW
  simp only [intervalIntegral.integral_const, smul_eq_mul] at h
  exact h.trans (by linarith)

noncomputable def tailW (u : ℝ) : ℝ := wPrimitive (u + 1) - wPrimitive 2

noncomputable def regIntegral (t : ℝ) : ℝ := ∫ u in (1 : ℝ)..t + 1, W u * tailW u

theorem tailW_measurable : Measurable tailW := by
  unfold tailW wPrimitive
  fun_prop

theorem tailW_eq_mass {u : ℝ} (hu : 1 ≤ u) : tailW u = wMass 2 (u + 1) := by
  rw [wMass_eq (by norm_num) (by linarith : 0 < u + 1)]
  rfl

theorem tailW_nonneg {u : ℝ} (hu : 1 ≤ u) : 0 ≤ tailW u := by
  rw [tailW_eq_mass hu]
  exact wMass_nonneg (by norm_num) (by linarith)

theorem tailW_continuousAt {u : ℝ} (hu : 0 < u) : ContinuousAt tailW u := by
  have hc := (wPrimitive_deriv (by linarith : 0 < u + 1)).continuousAt
  exact (hc.comp (f := fun x : ℝ ↦ x + 1) (x := u)
    (continuousAt_id.add continuousAt_const)).sub continuousAt_const

theorem regKernel_continuousOn {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun u ↦ W u * tailW u) (Icc a b) := by
  intro u hu
  have hu0 : 0 < u := ha.trans_le hu.1
  exact ((W_continuousAt (ne_of_gt hu0)).mul (tailW_continuousAt hu0)).continuousWithinAt

theorem wKernel_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable W volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro u hu
  rw [uIcc_of_le hab] at hu
  exact (W_continuousAt (ne_of_gt (ha.trans_le hu.1))).continuousWithinAt

theorem regIntegral_lower {t : ℝ} (ht : 2 ≤ t) :
    (1 : ℝ) / 3 * wMass 2 (t + 1) ≤ regIntegral t := by
  have h12 : IntervalIntegrable (fun u ↦ W u * tailW u) volume 1 2 :=
    (regKernel_continuousOn (b := 2) (by norm_num : (0 : ℝ) < 1)).intervalIntegrable_of_Icc (by norm_num)
  have h2T : IntervalIntegrable (fun u ↦ W u * tailW u) volume 2 (t + 1) :=
    (regKernel_continuousOn (b := t + 1) (by norm_num : (0 : ℝ) < 2)).intervalIntegrable_of_Icc (by linarith)
  have hfirst : 0 ≤ ∫ u in (1 : ℝ)..2, W u * tailW u := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro u hu
    exact mul_nonneg (W_pos (by linarith [hu.1])).le (tailW_nonneg hu.1)
  have hbound : (1 : ℝ) / 3 * wMass 2 (t + 1) ≤ ∫ u in (2 : ℝ)..t + 1, W u * tailW u := by
    unfold wMass
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by linarith)
      ((wKernel_intervalIntegrable (by norm_num) (by linarith : (2 : ℝ) ≤ t + 1)).const_mul _) h2T
    intro u hu
    have htail : (1 : ℝ) / 3 ≤ tailW u := by
      rw [tailW_eq_mass (by linarith [hu.1])]
      exact wMass_two_three_lower.trans (wMass_mono_right (by norm_num) (by norm_num) (by linarith [hu.1]))
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left htail (W_pos (by linarith [hu.1])).le
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h12 h2T
  unfold regIntegral
  linarith

theorem regIntegral_nonneg {t : ℝ} (ht : 2 ≤ t) : 0 ≤ regIntegral t :=
  le_trans (mul_nonneg (by norm_num) (wMass_nonneg (by norm_num) (by linarith))) (regIntegral_lower ht)

theorem initial_integral_le {s t : ℝ} (hs : 199 / 100 ≤ s) (hsup : s ≤ 23 / 10) (ht : 2 ≤ t) :
    wMass (s - 1) (t + 1) ≤ 48 * regIntegral t := by
  have ha : 0 < s - 1 := by linarith
  have hsplit : wMass (s - 1) (t + 1) = wMass (s - 1) 2 + wMass 2 (t + 1) := by
    rw [wMass_eq ha (by linarith), wMass_eq ha (by norm_num), wMass_eq (by norm_num) (by linarith)]
    ring
  have hsmall := wMass_initial_upper (a := s - 1) (by linarith) (by linarith)
  have hbig : (1 : ℝ) / 3 ≤ wMass 2 (t + 1) :=
    wMass_two_three_lower.trans (wMass_mono_right (by norm_num) (by norm_num) (by linarith))
  have hreg := regIntegral_lower ht
  rw [hsplit]
  linarith

end Erdos970Dependency.WeightIntegrals

end

end Erdos970

end OAI
