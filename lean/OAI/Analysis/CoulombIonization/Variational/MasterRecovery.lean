import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.CoulombLipschitzDuality
import OAI.Analysis.CoulombIonization.Variational.LocalWidthKernel

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped NNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis

noncomputable def masterTestConstant {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgs : tsupport g ⊆ ball 0 1) : ℝ≥0 :=
  (masterKernel_uniform_test_constants hg hgs).choose

lemma masterTestConstant_pos {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgs : tsupport g ⊆ ball 0 1) : 0 < masterTestConstant hg hgs :=
  (masterKernel_uniform_test_constants hg hgs).choose_spec.1

lemma masterKernel_test_support {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgs : tsupport g ⊆ ball 0 1) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (y : Space) :
    Function.support (fun x => masterKernel c₁ r₀ s g x y) ⊆
      closedBall y (2*masterWidth c₁ r₀ s y) :=
  ((masterKernel_uniform_test_constants hg hgs).choose_spec.2 c₁ r₀ s hc hcL hr hs hs1 y).1

lemma masterKernel_test_lipschitz {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgs : tsupport g ⊆ ball 0 1) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (y : Space) :
    LipschitzWith ⟨(masterTestConstant hg hgs:ℝ)*(masterWidth c₁ r₀ s y)⁻¹^4, by positivity⟩
      (fun x => masterKernel c₁ r₀ s g x y) :=
  ((masterKernel_uniform_test_constants hg hgs).choose_spec.2 c₁ r₀ s hc hcL hr hs hs1 y).2

def masterCenteredKernel (c₁ r₀ s : ℝ) (g : Space → ℝ) (y x : Space) : ℝ :=
  masterKernel c₁ r₀ s g (y+x) y

lemma masterCenteredKernel_support {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgs : tsupport g ⊆ ball 0 1) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (y : Space) :
    Function.support (masterCenteredKernel c₁ r₀ s g y) ⊆
      closedBall 0 (2*masterWidth c₁ r₀ s y) := by
  intro x hx
  have hh := masterKernel_test_support hg hgs hc hcL hr hs hs1 y hx
  simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left,sub_zero] using hh

lemma masterCenteredKernel_lipschitz {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgs : tsupport g ⊆ ball 0 1) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (y : Space) :
    LipschitzWith ⟨(masterTestConstant hg hgs:ℝ)*(masterWidth c₁ r₀ s y)⁻¹^4, by positivity⟩
      (masterCenteredKernel c₁ r₀ s g y) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  have hh := (masterKernel_test_lipschitz hg hgs hc hcL hr hs hs1 y).dist_le_mul (y+x) (y+z)
  simpa only [masterCenteredKernel,dist_add_left] using hh

lemma masterRecovery_coefficient {t C : ℝ} (ht : 0 < t) :
    16*(2*t)^3*(C*t⁻¹^4)^2 = 128*C^2*t⁻¹^5 := by
  field_simp [ht.ne']
  ring

theorem masterKernel_patch_recovery {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgs : tsupport g ⊆ ball 0 1) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (y : Space)
    {R : ℝ} (hR : 4*masterWidth c₁ r₀ s y < R)
    (T : ℝ) (hT : 0 < T) (Φ : TFField R)
    {σ : TFLp (ballMeasure R)} (hσ : NonnegDensity σ) :
    (∫ x, masterCenteredKernel c₁ r₀ s g y x*
      (σ-tfPatchMinimizer R T hT Φ) x ∂ballMeasure R)^2 ≤
      (128*(masterTestConstant hg hgs:ℝ)^2*(masterWidth c₁ r₀ s y)⁻¹^5)*
        tfPatchGap R T hT Φ σ := by
  have hpos := masterWidth_pos hc hr hs y
  have hh := tfPatchGap_lipschitz_control (by positivity : 0 < 2*masterWidth c₁ r₀ s y)
    (by linarith : 2*(2*masterWidth c₁ r₀ s y) < R) T hT Φ hσ
    (masterCenteredKernel_lipschitz hg hgs hc hcL hr hs hs1 y)
    (masterCenteredKernel_support hg hgs hc hcL hr hs hs1 y)
  change _ ≤ (16*(2*masterWidth c₁ r₀ s y)^3*
    ((masterTestConstant hg hgs:ℝ)*(masterWidth c₁ r₀ s y)⁻¹^4)^2)*_ at hh
  rw [masterRecovery_coefficient hpos] at hh
  exact hh

end CoulombAtom

end

end OAI
