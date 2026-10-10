import OAI.Probability.SLE.Multipoint.MultipointRadiusStatus
import OAI.Probability.SLE.Multipoint.MultipointSuccess

namespace OAI

/-! The source-normalized parameters for the physical multipoint estimate.
All constants depend only on the SLE parameter and the finite order. -/

noncomputable section
open Set
open scoped BigOperators

namespace SLEExactGauge.Multipoint

def sourceBeta (κ : ℝ) : ℝ := beta (2/κ) (greenExponent κ)

def sourceTarget (κ b e : ℝ) : ℝ := κ/4*Real.log (b/e)

lemma source_parameters {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) :
    0 < greenExponent κ ∧ 0 < sourceBeta κ ∧ sourceBeta κ ≤ 1 ∧
      2*(exponent (greenExponent κ)*sourceBeta κ) < 2/κ ∧
      2*(exponent (greenExponent κ)*(κ*sourceBeta κ)) < 2 := by
  have hp : 0 < greenExponent κ := by
    unfold greenExponent
    rw [sub_pos,lt_div_iff₀ hκ]
    linarith
  have ha : 0 < 2/κ := div_pos (by norm_num) hκ
  have hdecay := twice_exponent_beta_lt ha hp
  refine ⟨hp,beta_pos ha hp,beta_le_one _ _,hdecay,?_⟩
  have hscaled := (source_pair_exponent_admissible (c := exponent (greenExponent κ)*sourceBeta κ) hκ).mpr hdecay
  convert hscaled using 1
  ring

lemma sourceTarget_nonneg {κ b e : ℝ} (hκ : 0 ≤ κ) (he : 0 < e) (heb : e ≤ b) :
    0 ≤ sourceTarget κ b e := by
  exact mul_nonneg (div_nonneg hκ (by norm_num))
    (Real.log_nonneg ((one_le_div he).mpr heb))

lemma physical_radius_level_parameters {κ : ℝ} (hκ : 0 < κ)
    (z : ℂ) (R b e : ℝ) (he : 0 < e) (heb : e ≤ b) (hbR : b ≤ R) :
    let u₀ := Real.log (R/b)
    let u₂ := Real.log (R/e)
    0 ≤ u₀ ∧ u₀ ≤ u₂ ∧ 0 ≤ sourceTarget κ b e ∧
      sourceClockLevel κ z u₂ = sourceClockLevel κ z u₀ + sourceTarget κ b e ∧
      sourceClockLevel κ z ((u₀+u₂)/2) =
        sourceClockLevel κ z u₀ + sourceTarget κ b e/2 := by
  dsimp only
  have hb := he.trans_le heb
  have hR := hb.trans_le hbR
  have h₀ : 0 ≤ Real.log (R/b) := Real.log_nonneg ((one_le_div hb).mpr hbR)
  have h₂ : Real.log (R/b) ≤ Real.log (R/e) :=
    Real.log_le_log (div_pos hR hb) (div_le_div_of_nonneg_left hR.le he heb)
  have hgap : Real.log (R/e)-Real.log (R/b) = Real.log (b/e) := by
    rw [Real.log_div hR.ne' he.ne',Real.log_div hR.ne' hb.ne',Real.log_div hb.ne' he.ne']
    ring
  refine ⟨h₀,h₂,sourceTarget_nonneg hκ.le he heb,?_,?_⟩
  · unfold sourceClockLevel sourceTarget
    rw [← hgap]
    ring
  · unfold sourceClockLevel sourceTarget
    rw [← hgap]
    ring

lemma physical_switch_level_parameters {κ : ℝ} (hκ : 0 < κ)
    (z : ℂ) (R b e : ℝ) (he : 0 < e) (heb : e ≤ b) (hbR : b ≤ R) :
    (∀ j, 0 ≤ switchLevel R b e j) ∧ Monotone (switchLevel R b e) ∧
      sourceClockLevel κ z (switchLevel R b e 1) =
        sourceClockLevel κ z (switchLevel R b e 0) + sourceTarget κ b e/2 ∧
      sourceClockLevel κ z (switchLevel R b e 2) =
        sourceClockLevel κ z (switchLevel R b e 0) + sourceTarget κ b e := by
  obtain ⟨_,_,_,hend,hmid⟩ := physical_radius_level_parameters hκ z R b e he heb hbR
  refine ⟨fun j => switchLevel_nonneg he heb hbR j,
    switchLevel_monotone he heb hbR,?_,?_⟩
  · simpa [switchLevel] using hmid
  · simpa [switchLevel] using hend

lemma sourceClockLevel_physical_activation (κ : ℝ) (J : ℂ → ℂ) (z : ℂ)
    (hz : 0 < z.im) (R b : ℝ) (hR : 0 < R) (hb : 0 < b)
    (hRdef : R = 2*z.im*‖deriv J z‖) :
    sourceClockLevel κ z (Real.log (R/b)) = κ/4*Real.log (2*‖deriv J z‖/b) := by
  have hd : ‖deriv J z‖ ≠ 0 := by
    intro he
    rw [hRdef,he,mul_zero] at hR
    exact (lt_irrefl 0 hR)
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  unfold sourceClockLevel
  rw [hRdef,Real.log_div (mul_ne_zero (mul_ne_zero h2 hz.ne') hd) hb.ne',
    Real.log_mul (mul_ne_zero h2 hz.ne') hd,Real.log_mul h2 hz.ne',
    Real.log_div (mul_ne_zero h2 hd) hb.ne',Real.log_mul h2 hd]
  ring

lemma sourceTarget_coefficient {κ : ℝ} (hκ : 0 < κ) :
    1/(2*(2/κ)) = κ/4 := by field_simp [hκ.ne']; ring

lemma source_terminal_exponent {κ : ℝ} (hκ : 0 < κ) :
    greenExponent κ/(4*(2/κ)) = 1-κ/8 := by
  unfold greenExponent
  field_simp [hκ.ne']
  ring

lemma source_radius_targets_exponential {ι : Type*} (s : Finset ι)
    {κ : ℝ} (hκ : 0 < κ) (b e : ι → ℝ)
    (hb : ∀ i ∈ s, 0 < b i) (he : ∀ i ∈ s, 0 < e i) :
    Real.exp (-greenExponent κ/2 * ∑ i ∈ s, sourceTarget κ (b i) (e i)) =
      ∏ i ∈ s, (e i/b i)^(1-κ/8) := by
  have h := radius_targets_exponential s (a := 2/κ) (p := greenExponent κ)
    (show 0 < (2 : ℝ)/κ from div_pos (by norm_num) hκ) b e hb he
  simpa only [sourceTarget,sourceTarget_coefficient hκ,source_terminal_exponent hκ] using h

lemma source_successBarrier_inv {ι : Type*} (s : Finset ι)
    {κ : ℝ} (hκ : 0 < κ) (K : ℝ) (b e : ι → ℝ)
    (hb : ∀ i ∈ s, 0 < b i) (he : ∀ i ∈ s, 0 < e i) :
    (successBarrier (greenExponent κ) K s (fun i => sourceTarget κ (b i) (e i)))⁻¹ =
      (3 : ℝ)^s.card * Real.exp K * ∏ i ∈ s, (e i/b i)^(1-κ/8) := by
  rw [successBarrier_inv,source_radius_targets_exponential s hκ b e hb he]

end SLEExactGauge.Multipoint

end

end OAI
