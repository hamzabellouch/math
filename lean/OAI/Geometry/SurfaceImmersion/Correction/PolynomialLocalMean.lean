import OAI.Geometry.SurfaceImmersion.Correction.PolynomialLocalAmplitude
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialModeBudgets
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialFrameEnvelope

namespace OAI

/-! Quantitative mean estimates for the actual local construction. The
power depends on the fixed derivative and accuracy orders only. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes RootMean WeightedEstimates FiniteMean

variable {U V : Set Base} {s r ρ R : ℝ} {reference : Base → Tensor}
  {F : RField 4} {ψ : Base → ℝ} {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base}

lemma outputFactor_le_coefficientBudget (d : Budgets U V s F ψ Q χ e)
    (m : ℕ) {B : ℝ} (hB : 1 ≤ B) (hc : d.chi m ≤ B) (hp : d.pull m ≤ B) :
    outputFactor d m ≤ coefficientBudget m B := by
  have hχ := d.chi_pos m
  have hP := d.pull_pos m
  unfold outputFactor coefficientBudget
  gcongr

theorem polynomial_local_mean_estimates (q m : ℕ) :
    ∃ p : ℕ, ∃ C : ℝ, 1 ≤ C ∧
    ∀ {U V : Set Base} {s r ρ R : ℝ} {reference : Base → Tensor}
      {F : RField 4} {ψ : Base → ℝ} {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base},
      ∀ (_h : LocalBounds U V s r ρ R reference F ψ Q χ e)
        (d : Budgets U V s F ψ Q χ e),
      0 < s → s ≤ 1 → 0 < ρ → ∀ B : ℝ, 1 ≤ B → ρ⁻¹ ≤ B →
      d.inv (m+q+2) ≤ B → d.forms (m+q+2) ≤ B → d.psi (m+q+2) ≤ B →
      d.mode (m+q+2) ≤ B → d.normal (m+q+2) ≤ B → d.chi m ≤ B → d.pull m ≤ B →
    ∀ δ η : ℝ, 0 < δ → 0 < η → η ≤ 1 →
    ∀ (A A' : Base → Tensor) (D : ℝ), 0 ≤ D →
      ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ A' U →
      InTrialBall U reference r A → InTrialBall U reference r A' →
      WeightedBound U s (m+q+2) B A → WeightedBound U s (m+q+2) B A' →
      WeightedBound U s (m+q+2) D (A-A') →
      WeightedBound U s m (η*(C*B^p)) (meanTerm δ s F ψ Q χ e q η A) ∧
      WeightedBound U s m ((C*B^p)*η*D)
        (meanTerm δ s F ψ Q χ e q η A-meanTerm δ s F ψ Q χ e q η A') := by
  obtain ⟨a,C₀,hC₀,hamp⟩ := polynomial_local_amplitude_bounds (m+q+2)
  let Z := fun B : ℝ => meanErrorConstant 4 m B q *
    (Real.sqrt 2 * 2^(m+q+2)*B)^2*(C₀*B^a)^2
  have hZ : HasPolynomialBound Z :=
    ((meanErrorConstant_polynomial 4 m q).mul
      ((((polynomialBound_const (by positivity)).mul (polynomialBound_const (by positivity))).mul
        polynomialBound_id).pow 2)).mul
      (((polynomialBound_const (zero_le_one.trans hC₀)).mul (polynomialBound_id.pow a)).pow 2)
  obtain ⟨p,C,hC,hpoly⟩ := (polynomialBound_const zero_le_one).add
    (((polynomialBound_const (show (0:ℝ) ≤ 2 by norm_num)).mul (coefficientBudget_polynomial m)).mul hZ)
  refine ⟨p,C,hC,?_⟩
  intro U V s r ρ R reference F ψ Q χ e h d hs hs1 hρ B hB hρB hi hf hψ hm hn hχ hp δ η hδ hη hη1 A A' D hD hA hA' hball hball' hbA hbA' hbD
  obtain ⟨ha,ha',had⟩ := hamp h d hs hs1 hρ B hB hρB hi hf hψ A A' D hD hA hA' hball hball' hbA hbA' hbD
  have hB0 := zero_le_one.trans hB
  have hAB : 0 ≤ C₀*B^a := by positivity
  have hsa := h.amplitude_smooth hρ hA hball
  have hsb := h.amplitude_smooth hρ hA' hball'
  have hτs : η*s ≤ s := mul_le_of_le_one_left hs.le hη1
  have hcancel : η*s/s = η := mul_div_cancel_right₀ _ hs.ne'
  have hcoeff := (d.mode_bound (m+q+2)).mono_const hm
  have hnormal := (d.normal_bound (m+q+2)).mono_const hn
  have hval := weighted_meanTensor h.smoothF h.domain hsa hδ (mul_pos hη hs) hs hτs hs1
    hB0 hAB hB0 q m hcoeff ha hnormal
  have hval' : WeightedBound V s m (Z B*η)
      (meanTensor δ (η*s) F (phaseAmplitude ψ (coefficient Q e A)) q) := by
    convert hval using 1
    rw [hcancel]
    dsimp [Z]
    ring
  have hz : 0 ≤ Z B := by
    have hh := meanErrorConstant_nonneg 4 m q hB0
    dsimp [Z]
    positivity
  have hv := h.transport_bound d hs hs1 (mul_nonneg hz hη.le)
    (contDiffOn_meanTensor h.smoothF h.domain hsa δ (η*s) q) hval'
  have hdiff := weighted_meanTensor_difference h.smoothF h.domain hsa hsb hδ
    (mul_pos hη hs) hs hτs hs1 hB0 hAB (mul_nonneg hAB hD) hB0 q m hcoeff ha ha' had hnormal
  have hdiff' : WeightedBound V s m (2*Z B*D*η)
      (fun x => meanTensor δ (η*s) F (phaseAmplitude ψ (coefficient Q e A)) q x-
        meanTensor δ (η*s) F (phaseAmplitude ψ (coefficient Q e A')) q x) := by
    convert hdiff using 1
    rw [hcancel]
    dsimp [Z]
    ring
  have hd := h.transport_bound d hs hs1 (by positivity)
    ((contDiffOn_meanTensor h.smoothF h.domain hsa δ (η*s) q).sub
      (contDiffOn_meanTensor h.smoothF h.domain hsb δ (η*s) q)) hdiff'
  have hout := outputFactor_le_coefficientBudget d m hB hχ hp
  have hbudget : 1+2*coefficientBudget m B*Z B ≤ C*B^p := (hpoly B hB).2
  have hb0 : 0 ≤ coefficientBudget m B := by unfold coefficientBudget; positivity
  have hvalue : outputFactor d m*Z B ≤ C*B^p :=
    (mul_le_mul_of_nonneg_right hout hz).trans (by nlinarith [mul_nonneg hb0 hz])
  have hdifference : 2*outputFactor d m*Z B ≤ C*B^p := by
    have hh := mul_le_mul_of_nonneg_right hout (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hz)
    nlinarith
  constructor
  · apply hv.mono_const
    calc
      _ = η*(outputFactor d m*Z B) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hvalue hη.le
  · apply (hd.mono_const (show outputFactor d m*(2*Z B*D*η) ≤ C*B^p*η*D from by
      calc
        _ = (2*outputFactor d m*Z B)*(η*D) := by ring
        _ ≤ _ := by simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right hdifference (mul_nonneg hη.le hD))).congr
    intro x hx
    exact (map_sub (pullbackField χ x) _ _).symm

end ClosedSurfaceR4.PhaseMean

end

end OAI
