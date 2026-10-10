import OAI.NumberTheory.CubicMoment.Estimates.HeckeLogDerivativeBand

namespace OAI

/-! A single logarithmic width and a log-squared bound for an entire finite
Hecke contour. All zero-free information is derived from the analytic pair. -/
noncomputable section
namespace CubicFirstMoment

def heckeZeroFreeWidth (u : ℝ) : ℝ :=
  1/(32*(1+heckePairLogConstant)*(1+Real.log u))

def heckeLogSquaredConstant : ℝ :=
  ((diskLogDerivativeConstant+192*(1+heckePairLogConstant)/
    Real.log ((7/8:ℝ)/(3/4:ℝ)))/3)*(Real.log heckeDiskPolynomialConstant+12)

lemma heckeZeroFreeWidth_pos {u : ℝ} (hu : 10 ≤ u) : 0 < heckeZeroFreeWidth u := by
  have hl : 0 < Real.log u := Real.log_pos (by linarith)
  have hC := heckePairLogConstant_pos
  unfold heckeZeroFreeWidth
  positivity

lemma heckeZeroFreeWidth_le_one {u : ℝ} (hu : 10 ≤ u) : heckeZeroFreeWidth u ≤ 1 := by
  have hl : 0 < Real.log u := Real.log_pos (by linarith)
  have hC := heckePairLogConstant_pos
  unfold heckeZeroFreeWidth
  apply (div_le_one (by positivity)).mpr
  nlinarith

lemma heckeZeroFreeWidth_le_log {u : ℝ} (hu : 10 ≤ u) :
    heckeZeroFreeWidth u ≤ 1/(32*heckePairLogConstant*Real.log u) := by
  have hl : 0 < Real.log u := Real.log_pos (by linarith)
  have hC := heckePairLogConstant_pos
  unfold heckeZeroFreeWidth
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

lemma heckeLogSquaredConstant_pos : 0 < heckeLogSquaredConstant := by
  have hD := diskLogDerivativeConstant_pos
  have hC := heckePairLogConstant_pos
  have hP := Real.log_pos heckeDiskPolynomialConstant_gt_one
  have hr : 0 < Real.log ((7/8:ℝ)/(3/4:ℝ)) := Real.log_pos (by norm_num)
  unfold heckeLogSquaredConstant
  positivity

lemma heckeLogDerivativeBand_le_log_squared {u : ℝ} (hu : 10 ≤ u) :
    ((diskLogDerivativeConstant+1/((heckeZeroFreeWidth u/6)*
      Real.log ((7/8:ℝ)/(3/4:ℝ))))/3)*
      (Real.log heckeDiskPolynomialConstant+12*Real.log u) ≤
    heckeLogSquaredConstant*(1+Real.log u)^2 := by
  have hl : 0 < Real.log u := Real.log_pos (by linarith)
  have hD := diskLogDerivativeConstant_pos
  have hC := heckePairLogConstant_pos
  have hP := Real.log_pos heckeDiskPolynomialConstant_gt_one
  have hr : 0 < Real.log ((7/8:ℝ)/(3/4:ℝ)) := Real.log_pos (by norm_num)
  have he : 1/((heckeZeroFreeWidth u/6)*Real.log ((7/8:ℝ)/(3/4:ℝ))) =
      (192*(1+heckePairLogConstant)/Real.log ((7/8:ℝ)/(3/4:ℝ)))*
        (1+Real.log u) := by
    unfold heckeZeroFreeWidth
    field_simp
    ring
  rw [he]
  have hfirst : (diskLogDerivativeConstant+
      (192*(1+heckePairLogConstant)/Real.log ((7/8:ℝ)/(3/4:ℝ)))*(1+Real.log u))/3 ≤
      ((diskLogDerivativeConstant+192*(1+heckePairLogConstant)/
        Real.log ((7/8:ℝ)/(3/4:ℝ)))/3)*(1+Real.log u) := by nlinarith
  have hsecond : Real.log heckeDiskPolynomialConstant+12*Real.log u ≤
      (Real.log heckeDiskPolynomialConstant+12)*(1+Real.log u) := by nlinarith
  calc
    _ ≤ (((diskLogDerivativeConstant+192*(1+heckePairLogConstant)/
        Real.log ((7/8:ℝ)/(3/4:ℝ)))/3)*(1+Real.log u))*
      ((Real.log heckeDiskPolynomialConstant+12)*(1+Real.log u)) :=
        mul_le_mul hfirst hsecond (by positivity) (by positivity)
    _ = _ := by unfold heckeLogSquaredConstant; ring

theorem hecke_logDeriv_norm_uniform_of_band
    {χ : EisensteinIdealExponent → ℂ} (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hχ0 : χ 0=1) (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ)
    {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    {A k u T : ℝ} {ε : ℂ}
    (hA : 0 < A) (hk : 0 ≤ k) (hε : ‖ε‖ ≤ 1) (hu : 10 ≤ u)
    (huA : A ≤ u) (huk : k+7 ≤ u) (huT : 4+2*(T+3) ≤ u)
    (hb : ∀ t z, |t| ≤ T → ‖z‖ ≤ (7/8:ℝ) →
      ‖normalizedHeckeDisk L t z‖ ≤ normalizedHeckeDiskBound A k ε t)
    (hzero : ∀ s : ℂ, |s.im| ≤ T+3 → 1-heckeZeroFreeWidth u < s.re → L s ≠ 0)
    {σ t : ℝ} (hσ : 1-heckeZeroFreeWidth u/2 ≤ σ) (hσ2 : σ ≤ 2) (ht : |t| ≤ T) :
    ‖logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)‖ ≤
      heckeLogSquaredConstant*(1+Real.log u)^2 := by
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  have hut : 4+|t| ≤ u := by linarith
  have hlog := normalizedHeckeDiskBound_log hA hk hε (by linarith) huA huk hut
  have hband := hecke_logDeriv_norm_of_zero_free_band hχ hχ0 hχadd hL hs
    (normalizedHeckeDiskBound_gt_one A k ε t) (heckeZeroFreeWidth_pos hu)
    (heckeZeroFreeWidth_le_one hu) hσ hσ2 (fun z hz => hb t z ht hz) (by
      intro s him hre
      apply hzero s _ hre
      calc
        |s.im| = |(s.im-t)+t| := by congr 1; ring
        _ ≤ |s.im-t|+|t| := abs_add_le _ _
        _ ≤ T+3 := by linarith)
  exact hband.trans ((mul_le_mul_of_nonneg_left hlog (by
    have hD := diskLogDerivativeConstant_pos
    have hw := heckeZeroFreeWidth_pos hu
    have hr : 0 < Real.log ((7/8:ℝ)/(3/4:ℝ)) := Real.log_pos (by norm_num)
    positivity)).trans (heckeLogDerivativeBand_le_log_squared hu))

theorem hecke_logDeriv_norm_uniform_from_analytic_pair
    {χ χdual χ2dual : EisensteinIdealExponent → ℂ} (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hχ0 : χ 0=1) (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ)
    (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1) (hχ2dual : ∀ ν, ‖χ2dual ν‖ ≤ 1)
    {L Ldual L2 L2dual : ℂ → ℂ} (hL : Differentiable ℂ L) (hL2 : Differentiable ℂ L2)
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    (hs2 : ∀ s : ℂ, 1 < s.re → L2 s=normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm s)
    (hds : ∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s)
    (hds2 : ∀ s : ℂ, 1 < s.re → L2dual s=normDirichletSeries χ2dual idealExponentNorm s)
    {A A2 k k2 u T : ℝ} {ε ε2 : ℂ}
    (hA : 0 < A) (hA2 : 0 < A2) (hk : 0 ≤ k) (hk2 : 0 ≤ k2)
    (hε : ‖ε‖ ≤ 1) (hε2 : ‖ε2‖ ≤ 1) (hu : 10 ≤ u)
    (huA : A ≤ u) (huA2 : A2 ≤ u) (huk : k+7 ≤ u) (huk2 : k2+7 ≤ u)
    (huT : 4+2*(T+3) ≤ u)
    (hFE : HeckeFunctionalEquation A k ε L Ldual)
    (hFE2 : HeckeFunctionalEquation A2 k2 ε2 L2 L2dual)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L)
    (hcomp2 : ShiftedCompletedHeckeFiniteOrder A2 k2 L2)
    {σ t : ℝ} (hσ : 1-heckeZeroFreeWidth u/2 ≤ σ) (hσ2 : σ ≤ 2) (ht : |t| ≤ T) :
    ‖logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)‖ ≤
      heckeLogSquaredConstant*(1+Real.log u)^2 := by
  apply hecke_logDeriv_norm_uniform_of_band hχ hχ0 hχadd hL hs
    hA hk hε hu huA huk huT _ _ hσ hσ2 ht
  · intro t z _ hz
    exact normalizedHeckeDisk_bound hχ hχ0 hχadd hχdual hA hk hL hs hds hFE hcomp t z
      (hz.trans (by norm_num))
  · intro s him hre
    have hT : 0 ≤ T := (abs_nonneg t).trans ht
    have hheight : 4+|s.im| ≤ u := by linarith
    have hheight2 : 4+|2*s.im| ≤ u := by
      rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith
    have heq : (s.re:ℂ)+(s.im:ℂ)*Complex.I=s := Complex.re_add_im s
    rw [←heq]
    exact hecke_zero_free_log_from_analytic_pair hχ hχ0 hχadd hχdual hχ2dual hL hL2
      hs hs2 hds hds2 hA hA2 hk hk2 hε hε2 hu huA huA2 huk huk2 hheight hheight2
      hFE hFE2 hcomp hcomp2 (by linarith [heckeZeroFreeWidth_le_log hu])

end CubicFirstMoment

end

end OAI
