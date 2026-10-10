import OAI.NumberTheory.JointDickman.Amplification.RampCutoff
import OAI.NumberTheory.JointDickman.Amplification.CandidateFiniteCutoff

namespace OAI

/-! # A continuous approximation of the actual counting-scale cutoff -/

namespace JointDickman
open Finset

noncomputable def countingRamp (δ s x : ℝ) : ℝ := averagingRamp s (s+δ) x

theorem countingRamp_bounds {δ : ℝ} (hδ : 0 < δ) (s x : ℝ) :
    0 ≤ countingRamp δ s x ∧ countingRamp δ s x ≤ 1 :=
  averagingRamp_bounds (by linarith) x

theorem countingRamp_zero {δ s x : ℝ} (hδ : 0 < δ) (hx : x ≤ s) :
    countingRamp δ s x = 0 := averagingRamp_zero (by linarith) hx

theorem countingRamp_one {δ s x : ℝ} (hδ : 0 < δ) (hx : s+δ ≤ x) :
    countingRamp δ s x = 1 := averagingRamp_one (by linarith) hx

theorem countingRamp_continuous {δ : ℝ} (_hδ : 0 < δ) :
    Continuous (fun q : ℝ × ℝ => countingRamp δ q.1 q.2) := by
  have he (s x : ℝ) : countingRamp δ s x = (min (s+δ) (max s x)-s)/δ := by
    unfold countingRamp averagingRamp
    congr 1
    ring
  simp_rw [he]
  exact (((continuous_fst.add continuous_const).min (continuous_fst.max continuous_snd)).sub
    continuous_fst).div_const δ

open Classical in
theorem countingRamp_sharp_error {δ : ℝ} (hδ : 0 < δ) (s x : ℝ) :
    0 ≤ (if s < x then (1 : ℝ) else 0)-countingRamp δ s x ∧
      (if s < x then (1 : ℝ) else 0)-countingRamp δ s x ≤
        (if s < x ∧ x < s+δ then (1 : ℝ) else 0) := by
  by_cases hx : s < x
  · rw [ite_eq_left hx]
    by_cases hhi : x < s+δ
    · rw [ite_eq_left ⟨hx,hhi⟩]
      have hh := countingRamp_bounds hδ s x
      constructor <;> linarith
    · rw [ite_eq_right (fun hh => hhi hh.2),countingRamp_one hδ (le_of_not_gt hhi)]
      norm_num
  · rw [ite_eq_right hx,ite_eq_right (fun hh => hx hh.1),
      countingRamp_zero hδ (le_of_not_gt hx)]
    norm_num

open Classical in
theorem finiteCandidateCutoff_threshold {B T N u M : ℕ} (hT : 0 < T)
    (e : BlockCandidateIndex M) (hc : 0 < candidateQuotient e) :
    finiteCandidateCutoff B T N u e =
      (if ((u+(e.1.1.val+1) : ℕ) : ℝ)/((T : ℝ)*(N+1)) <
          (candidateLow e : ℝ)/((T : ℝ)*candidateQuotient e) then
        candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) e else 0) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hcr : (0 : ℝ) < candidateQuotient e := by exact_mod_cast hc
  have hden : (0 : ℝ) < (T : ℝ)*(N+1) := by positivity
  have he : (candidateQuotient e*(u+(e.1.1.val+1)) < candidateLow e*(N+1)) ↔
      ((u+(e.1.1.val+1) : ℕ) : ℝ)/((T : ℝ)*(N+1)) <
        (candidateLow e : ℝ)/((T : ℝ)*candidateQuotient e) := by
    rw [div_lt_div_iff₀ hden (mul_pos hTr hcr)]
    constructor
    · intro h
      have hh : (candidateQuotient e : ℝ)*(u+(e.1.1.val+1)) < (candidateLow e : ℝ)*(N+1) := by
        exact_mod_cast h
      have hm := mul_lt_mul_of_pos_left hh hTr
      convert hm using 1 <;> push_cast <;> ring
    · intro h
      have hm : (T : ℝ)*((candidateQuotient e : ℝ)*(u+(e.1.1.val+1))) <
          (T : ℝ)*((candidateLow e : ℝ)*(N+1)) := by convert h using 1 <;> push_cast <;> ring
      have hh := (mul_lt_mul_iff_right₀ hTr).mp hm
      exact_mod_cast hh
  unfold finiteCandidateCutoff
  by_cases h : candidateQuotient e*(u+(e.1.1.val+1)) < candidateLow e*(N+1)
  · rw [ite_eq_left h,ite_eq_left (he.mp h)]
  · rw [ite_eq_right h,ite_eq_right (fun hh => h (he.mpr hh))]

noncomputable def countingBand (δ s x : ℝ) : ℝ :=
  countingRamp δ (s-δ) x*(1-countingRamp δ (s+δ) x)

theorem countingBand_bounds {δ : ℝ} (hδ : 0 < δ) (s x : ℝ) :
    0 ≤ countingBand δ s x ∧ countingBand δ s x ≤ 1 := by
  have ha := countingRamp_bounds hδ (s-δ) x
  have hb := countingRamp_bounds hδ (s+δ) x
  unfold countingBand
  constructor
  · exact mul_nonneg ha.1 (by linarith)
  · nlinarith

theorem countingBand_continuous {δ : ℝ} (hδ : 0 < δ) :
    Continuous (fun q : ℝ × ℝ => countingBand δ q.1 q.2) := by
  have ha := (countingRamp_continuous hδ).comp
    (((continuous_fst.sub continuous_const).prodMk continuous_snd) :
      Continuous (fun q : ℝ × ℝ => (q.1-δ,q.2)))
  have hb := (countingRamp_continuous hδ).comp
    (((continuous_fst.add continuous_const).prodMk continuous_snd) :
      Continuous (fun q : ℝ × ℝ => (q.1+δ,q.2)))
  exact ha.mul (continuous_const.sub hb)

open Classical in
theorem countingRamp_error_le_band {δ : ℝ} (hδ : 0 < δ) (s x : ℝ) :
    |(if s < x then (1 : ℝ) else 0)-countingRamp δ s x| ≤ countingBand δ s x := by
  obtain ⟨hpos,hle⟩ := countingRamp_sharp_error hδ s x
  rw [abs_of_nonneg hpos]
  by_cases hx : s < x ∧ x < s+δ
  · have ha : countingRamp δ (s-δ) x = 1 :=
      countingRamp_one hδ (by linarith [hx.1])
    have hb : countingRamp δ (s+δ) x = 0 := countingRamp_zero hδ hx.2.le
    simp only [countingBand,ha,hb,sub_zero,mul_one]
    exact (countingRamp_bounds hδ s x).1 |> fun hh => by
      rw [ite_eq_left hx.1]; linarith
  · rw [ite_eq_right hx] at hle
    exact hle.trans (countingBand_bounds hδ s x).1

theorem countingBand_zero {δ s x : ℝ} (hδ : 0 < δ)
    (hx : x ≤ s-δ ∨ s+2*δ ≤ x) : countingBand δ s x = 0 := by
  rcases hx with hx | hx
  · simp only [countingBand,countingRamp_zero hδ hx,zero_mul]
  · have hh : countingRamp δ (s+δ) x = 1 := countingRamp_one hδ (by linarith)
    simp only [countingBand,hh,sub_self,mul_zero]

end JointDickman

end OAI
