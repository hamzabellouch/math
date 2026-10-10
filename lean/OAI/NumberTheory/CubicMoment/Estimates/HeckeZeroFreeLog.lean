import OAI.NumberTheory.CubicMoment.Estimates.HeckeDiskGrowth

namespace OAI

/-! The logarithmic zero-free width obtained from the actual polynomial
Hecke disk bounds, for a character and its square. -/
noncomputable section
namespace CubicFirstMoment

theorem hecke_zero_free_log_of_disks
    {χ : EisensteinIdealExponent → ℂ} (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hχ0 : χ 0=1) (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ)
    {L L2 : ℂ → ℂ} (hL : Differentiable ℂ L) (hL2 : Differentiable ℂ L2)
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    (hs2 : ∀ s : ℂ, 1 < s.re → L2 s=normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm s)
    {A A2 k k2 u t : ℝ} {ε ε2 : ℂ}
    (hA : 0 < A) (hA2 : 0 < A2) (hk : 0 ≤ k) (hk2 : 0 ≤ k2)
    (hε : ‖ε‖ ≤ 1) (hε2 : ‖ε2‖ ≤ 1) (hu : 10 ≤ u)
    (huA : A ≤ u) (huA2 : A2 ≤ u) (huk : k+7 ≤ u) (huk2 : k2+7 ≤ u)
    (hut : 4+|t| ≤ u) (hut2 : 4+|2*t| ≤ u)
    (hb : ∀ z : ℂ, ‖z‖ ≤ (7/8:ℝ) →
      ‖normalizedHeckeDisk L t z‖ ≤ normalizedHeckeDiskBound A k ε t)
    (hb2 : ∀ z : ℂ, ‖z‖ ≤ (7/8:ℝ) →
      ‖normalizedHeckeDisk L2 (2*t) z‖ ≤ normalizedHeckeDiskBound A2 k2 ε2 (2*t))
    {β : ℝ} (hβ : 1-1/(32*heckePairLogConstant*Real.log u) < β) :
    L ((β:ℂ)+(t:ℂ)*Complex.I) ≠ 0 := by
  have he := heckePairZeroFreeError_log hA hA2 hk hk2 hε hε2 hu huA huA2 huk huk2 hut hut2
  have he1 := heckePairZeroFreeError_ge_one (normalizedHeckeDiskBound_gt_one A k ε t)
    (normalizedHeckeDiskBound_gt_one A2 k2 ε2 (2*t))
  have he0 : 0 < heckePairZeroFreeError (normalizedHeckeDiskBound A k ε t)
      (normalizedHeckeDiskBound A2 k2 ε2 (2*t)) := by linarith
  have hrec : 1/(32*heckePairLogConstant*Real.log u) ≤
      1/(32*heckePairZeroFreeError (normalizedHeckeDiskBound A k ε t)
        (normalizedHeckeDiskBound A2 k2 ε2 (2*t))) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  exact hecke_zero_free_of_disk_pair hχ hχ0 hχadd hL hL2 hs hs2
    (normalizedHeckeDiskBound_gt_one A k ε t)
    (normalizedHeckeDiskBound_gt_one A2 k2 ε2 (2*t)) hb hb2 (by linarith)

theorem hecke_zero_free_log_from_analytic_pair
    {χ χdual χ2dual : EisensteinIdealExponent → ℂ} (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hχ0 : χ 0=1) (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ)
    (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1) (hχ2dual : ∀ ν, ‖χ2dual ν‖ ≤ 1)
    {L Ldual L2 L2dual : ℂ → ℂ} (hL : Differentiable ℂ L) (hL2 : Differentiable ℂ L2)
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    (hs2 : ∀ s : ℂ, 1 < s.re → L2 s=normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm s)
    (hds : ∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s)
    (hds2 : ∀ s : ℂ, 1 < s.re → L2dual s=normDirichletSeries χ2dual idealExponentNorm s)
    {A A2 k k2 u t : ℝ} {ε ε2 : ℂ}
    (hA : 0 < A) (hA2 : 0 < A2) (hk : 0 ≤ k) (hk2 : 0 ≤ k2)
    (hε : ‖ε‖ ≤ 1) (hε2 : ‖ε2‖ ≤ 1) (hu : 10 ≤ u)
    (huA : A ≤ u) (huA2 : A2 ≤ u) (huk : k+7 ≤ u) (huk2 : k2+7 ≤ u)
    (hut : 4+|t| ≤ u) (hut2 : 4+|2*t| ≤ u)
    (hFE : HeckeFunctionalEquation A k ε L Ldual)
    (hFE2 : HeckeFunctionalEquation A2 k2 ε2 L2 L2dual)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L)
    (hcomp2 : ShiftedCompletedHeckeFiniteOrder A2 k2 L2)
    {β : ℝ} (hβ : 1-1/(32*heckePairLogConstant*Real.log u) < β) :
    L ((β:ℂ)+(t:ℂ)*Complex.I) ≠ 0 := by
  have hχ2 : ∀ ν, ‖(χ ν)^2‖ ≤ 1 := by
    intro ν
    rw [norm_pow]
    exact pow_le_one₀ (_root_.norm_nonneg _) (hχ ν)
  have hχ20 : (χ 0)^2=1 := by rw [hχ0]; norm_num
  have hχ2add : ∀ ν κ, (χ (ν+κ))^2=(χ ν)^2*(χ κ)^2 := by
    intro ν κ
    rw [hχadd,mul_pow]
  apply hecke_zero_free_log_of_disks hχ hχ0 hχadd hL hL2 hs hs2
    hA hA2 hk hk2 hε hε2 hu huA huA2 huk huk2 hut hut2
    (β := β) (hβ := hβ)
  · intro z hz
    exact normalizedHeckeDisk_bound hχ hχ0 hχadd hχdual hA hk hL hs hds hFE hcomp t z
      (hz.trans (by norm_num))
  · intro z hz
    exact normalizedHeckeDisk_bound hχ2 hχ20 hχ2add hχ2dual hA2 hk2 hL2 hs2 hds2 hFE2 hcomp2
      (2*t) z (hz.trans (by norm_num))

end CubicFirstMoment

end

end OAI
