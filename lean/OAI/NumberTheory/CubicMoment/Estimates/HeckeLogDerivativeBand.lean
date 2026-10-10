import OAI.NumberTheory.CubicMoment.Estimates.AnalyticDiskAbsoluteBound
import OAI.NumberTheory.CubicMoment.Estimates.HeckeZeroFreeLog

namespace OAI

/-! The absolute logarithmic-derivative bound on the inner half of a
zero-free band. This is the estimate used when shifting prime-sum contours. -/
noncomputable section
namespace CubicFirstMoment

theorem hecke_logDeriv_norm_of_zero_free_band
    {χ : EisensteinIdealExponent → ℂ} (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hχ0 : χ 0=1) (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ)
    {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    {B η t σ : ℝ} (hB : 1 < B) (hη : 0 < η) (hη1 : η ≤ 1)
    (hσ : 1-η/2 ≤ σ) (hσ2 : σ ≤ 2)
    (hb : ∀ z : ℂ, ‖z‖ ≤ (7/8:ℝ) → ‖normalizedHeckeDisk L t z‖ ≤ B)
    (hzeroFree : ∀ s : ℂ, |s.im-t| ≤ (9/4:ℝ) → 1-η < s.re → L s ≠ 0) :
    ‖logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)‖ ≤
      ((diskLogDerivativeConstant+1/((η/6)*Real.log ((7/8:ℝ)/(3/4:ℝ))))/3)*Real.log B := by
  let z : ℂ := ((σ-2:ℝ):ℂ)/3
  have hc : L (2+(t:ℂ)*Complex.I) ≠ 0 :=
    heckeSeries_ne_zero hχ hχ0 hχadd hs (by simp)
  have hzEq : 2+(t:ℂ)*Complex.I+3*z=(σ:ℂ)+(t:ℂ)*Complex.I := by
    dsimp [z]
    push_cast
    ring
  have hzN : ‖z‖ ≤ (1/2:ℝ) := by
    simp only [z,norm_div,Complex.norm_real,Real.norm_eq_abs,
      show ‖(3:ℂ)‖=3 by norm_num]
    rw [div_le_iff₀ (by norm_num)]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hLs : L ((σ:ℂ)+(t:ℂ)*Complex.I) ≠ 0 :=
    hzeroFree _ (by norm_num) (by simp; linarith)
  have hfz : normalizedHeckeDisk L t z ≠ 0 := by
    exact div_ne_zero (by rw [hzEq]; exact hLs) hc
  have hsep (w : ℂ) (hw : ‖w‖ ≤ (3/4:ℝ)) (hw0 : normalizedHeckeDisk L t w=0) :
      η/6 ≤ ‖z-w‖ := by
    have hroot : L (2+(t:ℂ)*Complex.I+3*w)=0 := (div_eq_zero_iff.mp hw0).resolve_right hc
    have him : |(2+(t:ℂ)*Complex.I+3*w).im-t| ≤ (9/4:ℝ) := by
      have hi := (Complex.abs_im_le_norm w).trans hw
      have he : (2+(t:ℂ)*Complex.I+3*w).im-t=3*w.im := by simp
      rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3)]
      linarith
    have hre : (2+(t:ℂ)*Complex.I+3*w).re ≤ 1-η := by
      by_contra h
      exact hzeroFree _ him (lt_of_not_ge h) hroot
    have hre' : 2+3*w.re ≤ 1-η := by simpa using hre
    have hdiff : (z-w).re=(σ-2)/3-w.re := by simp [z]
    have hrn := (le_abs_self ((z-w).re)).trans (Complex.abs_re_le_norm (z-w))
    rw [hdiff] at hrn
    linarith
  have hd := normalized_disk_logDeriv_norm_bound _
    (normalizedHeckeDisk_differentiable hL t) (normalizedHeckeDisk_zero t hc) hB
    (show 0 < η/6 by positivity) hb hzN hfz hsep
  rw [normalizedHeckeDisk_logDeriv hL t z hc,hzEq,norm_mul,
    show ‖(3:ℂ)‖=3 by norm_num] at hd
  linarith

end CubicFirstMoment

end

end OAI
