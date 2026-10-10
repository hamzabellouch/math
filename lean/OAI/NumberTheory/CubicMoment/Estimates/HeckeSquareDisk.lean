import OAI.NumberTheory.CubicMoment.Estimates.HeckeUniformLogDerivative
import OAI.NumberTheory.CubicMoment.Estimates.EulerHeckeDisk

namespace OAI

/-! The existing zero-free argument needs only the actual square series
and its normalized disk bound. This permits the proved finite Euler correction. -/
noncomputable section
namespace CubicFirstMoment

theorem hecke_zero_free_log_from_square_disk
    {χ χdual : EisensteinIdealExponent → ℂ} (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hχ0 : χ 0=1) (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ)
    (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {L Ldual L2 : ℂ → ℂ} (hL : Differentiable ℂ L) (hL2 : Differentiable ℂ L2)
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    (hs2 : ∀ s : ℂ, 1 < s.re → L2 s=normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm s)
    (hds : ∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s)
    {A A2 k k2 u t : ℝ} {ε ε2 : ℂ}
    (hA : 0 < A) (hA2 : 0 < A2) (hk : 0 ≤ k) (hk2 : 0 ≤ k2)
    (hε : ‖ε‖ ≤ 1) (hε2 : ‖ε2‖ ≤ 1) (hu : 10 ≤ u)
    (huA : A ≤ u) (huA2 : A2 ≤ u) (huk : k+7 ≤ u) (huk2 : k2+7 ≤ u)
    (hut : 4+|t| ≤ u) (hut2 : 4+|2*t| ≤ u)
    (hFE : HeckeFunctionalEquation A k ε L Ldual)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L)
    (hdisk2 : ∀ t z, ‖z‖ ≤ (7/8:ℝ) →
      ‖normalizedHeckeDisk L2 t z‖ ≤ normalizedHeckeDiskBound A2 k2 ε2 t)
    {β : ℝ} (hβ : 1-1/(32*heckePairLogConstant*Real.log u) < β) :
    L ((β:ℂ)+(t:ℂ)*Complex.I) ≠ 0 := by
  apply hecke_zero_free_log_of_disks hχ hχ0 hχadd hL hL2 hs hs2
    hA hA2 hk hk2 hε hε2 hu huA huA2 huk huk2 hut hut2
    (β := β) (hβ := hβ)
  · intro z hz
    exact normalizedHeckeDisk_bound hχ hχ0 hχadd hχdual hA hk hL hs hds hFE hcomp t z
      (hz.trans (by norm_num))
  · intro z hz
    exact hdisk2 (2*t) z hz

theorem hecke_logDeriv_norm_uniform_from_square_disk
    {χ χdual : EisensteinIdealExponent → ℂ} (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hχ0 : χ 0=1) (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ)
    (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {L Ldual L2 : ℂ → ℂ} (hL : Differentiable ℂ L) (hL2 : Differentiable ℂ L2)
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    (hs2 : ∀ s : ℂ, 1 < s.re → L2 s=normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm s)
    (hds : ∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s)
    {A A2 k k2 u T : ℝ} {ε ε2 : ℂ}
    (hA : 0 < A) (hA2 : 0 < A2) (hk : 0 ≤ k) (hk2 : 0 ≤ k2)
    (hε : ‖ε‖ ≤ 1) (hε2 : ‖ε2‖ ≤ 1) (hu : 10 ≤ u)
    (huA : A ≤ u) (huA2 : A2 ≤ u) (huk : k+7 ≤ u) (huk2 : k2+7 ≤ u)
    (huT : 4+2*(T+3) ≤ u)
    (hFE : HeckeFunctionalEquation A k ε L Ldual)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L)
    (hdisk2 : ∀ t z, ‖z‖ ≤ (7/8:ℝ) →
      ‖normalizedHeckeDisk L2 t z‖ ≤ normalizedHeckeDiskBound A2 k2 ε2 t)
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
    exact hecke_zero_free_log_from_square_disk hχ hχ0 hχadd hχdual hL hL2
      hs hs2 hds hA hA2 hk hk2 hε hε2 hu huA huA2 huk huk2 hheight hheight2
      hFE hcomp hdisk2 (by linarith [heckeZeroFreeWidth_le_log hu])

end CubicFirstMoment

end

end OAI
