import Mathlib
import OAI.Analysis.CoulombIonization.Variational.SmoothNewton

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_LipschitzMollifier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff Topology Convolution NNReal

lemma normalized_convolution_integrable {η g : TFSpace → ℝ}
    (hη : Continuous η) (hcη : HasCompactSupport η) (hg : Continuous g) (x : TFSpace) :
    Integrable (fun z => η z*g (x-z)) :=
  (hη.mul (hg.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport hcη.mul_right

lemma normalized_convolution_lipschitz {η g : TFSpace → ℝ} {L : ℝ≥0}
    (hη : Continuous η) (hcη : HasCompactSupport η)
    (hnη : ∀ x, 0 ≤ η x) (hmη : ∫ x, η x = 1) (hg : LipschitzWith L g) :
    LipschitzWith L (η ⋆[newtonMul] g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hi : Integrable η := hη.integrable_of_hasCompactSupport hcη
  have he : (η ⋆[newtonMul] g) x-(η ⋆[newtonMul] g) y =
      ∫ z, η z*(g (x-z)-g (y-z)) := by
    simp only [convolution,newtonMul,ContinuousLinearMap.mul_apply',mul_sub]
    rw [integral_sub (normalized_convolution_integrable hη hcη hg.continuous x)
      (normalized_convolution_integrable hη hcη hg.continuous y)]
  rw [dist_eq_norm,he]
  calc
    _ ≤ ∫ z, ((L:ℝ)*dist x y)*η z := norm_integral_le_of_norm_le
      (hi.const_mul _) (Eventually.of_forall fun z => by
        rw [norm_mul,Real.norm_of_nonneg (hnη z)]
        have hh := hg.dist_le_mul (x-z) (y-z)
        rw [dist_sub_right,dist_eq_norm] at hh
        nlinarith [mul_le_mul_of_nonneg_left hh (hnη z)])
    _ = _ := by rw [integral_const_mul,hmη,mul_one]

lemma normalized_convolution_error {η g : TFSpace → ℝ} {L : ℝ≥0} {r : ℝ}
    (hη : Continuous η) (hcη : HasCompactSupport η)
    (hnη : ∀ x, 0 ≤ η x) (hmη : ∫ x, η x = 1)
    (hsη : ∀ x, η x ≠ 0 → ‖x‖ ≤ r) (hg : LipschitzWith L g) (x : TFSpace) :
    ‖(η ⋆[newtonMul] g) x-g x‖ ≤ (L:ℝ)*r := by
  have hi : Integrable η := hη.integrable_of_hasCompactSupport hcη
  have he : (η ⋆[newtonMul] g) x-g x = ∫ z, η z*(g (x-z)-g x) := by
    simp only [convolution,newtonMul,ContinuousLinearMap.mul_apply',mul_sub]
    rw [integral_sub (normalized_convolution_integrable hη hcη hg.continuous x)
      (hi.mul_const _),integral_mul_const,hmη,one_mul]
  rw [he]
  calc
    _ ≤ ∫ z, ((L:ℝ)*r)*η z := norm_integral_le_of_norm_le (hi.const_mul _)
      (Eventually.of_forall fun z => by
        by_cases hz : η z = 0
        · simp [hz]
        · rw [norm_mul,Real.norm_of_nonneg (hnη z)]
          have hh := hg.dist_le_mul (x-z) x
          have hd : dist (x-z) x = ‖z‖ := by rw [dist_eq_norm]; simp
          rw [hd,dist_eq_norm] at hh
          have hl : ‖g (x-z)-g x‖ ≤ (L:ℝ)*r :=
            hh.trans (mul_le_mul_of_nonneg_left (hsη z hz) L.coe_nonneg)
          nlinarith [mul_le_mul_of_nonneg_left hl (hnη z)])
    _ = _ := by rw [integral_const_mul,hmη,mul_one]

lemma convolution_tsupport_bound {η g : TFSpace → ℝ} {r s : ℝ}
    (hsη : ∀ x, η x ≠ 0 → ‖x‖ ≤ r) (hsg : ∀ x, g x ≠ 0 → ‖x‖ ≤ s) :
    tsupport (η ⋆[newtonMul] g) ⊆ closedBall 0 (r+s) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  obtain ⟨u,hu,v,hv,rfl⟩ := support_convolution_subset newtonMul hx
  rw [mem_closedBall_zero_iff]
  exact (norm_add_le u v).trans (add_le_add (hsη u hu) (hsg v hv))

def packetSmooth (r : ℝ) (g : TFSpace → ℝ) : TFSpace → ℝ :=
  CoulombAtom.packetDensity 0 r ⋆[newtonMul] g

lemma packetSmooth_contDiff {r : ℝ} (hr : 0 < r) {g : TFSpace → ℝ} (hg : Continuous g) :
    ContDiff ℝ ∞ (packetSmooth r g) :=
  (CoulombAtom.packetDensity_compact 0 hr).contDiff_convolution_left newtonMul
    (CoulombAtom.packetDensity_smooth 0 r) hg.locallyIntegrable

lemma packetSmooth_compact {r : ℝ} (hr : 0 < r) {g : TFSpace → ℝ} (hg : HasCompactSupport g) :
    HasCompactSupport (packetSmooth r g) :=
  HasCompactSupport.convolution newtonMul (CoulombAtom.packetDensity_compact 0 hr) hg

lemma packetSmooth_lipschitz {r : ℝ} (hr : 0 < r) {g : TFSpace → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) : LipschitzWith L (packetSmooth r g) :=
  normalized_convolution_lipschitz (CoulombAtom.packetDensity_smooth 0 r).continuous
    (CoulombAtom.packetDensity_compact 0 hr) (CoulombAtom.packetDensity_nonneg 0 r)
    (CoulombAtom.packetDensity_mass 0 hr) hg

lemma packetSmooth_error {r : ℝ} (hr : 0 < r) {g : TFSpace → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (x : TFSpace) : ‖packetSmooth r g x-g x‖ ≤ (L:ℝ)*r :=
  normalized_convolution_error (CoulombAtom.packetDensity_smooth 0 r).continuous
    (CoulombAtom.packetDensity_compact 0 hr) (CoulombAtom.packetDensity_nonneg 0 r)
    (CoulombAtom.packetDensity_mass 0 hr)
    (fun z hz => by simpa only [sub_zero] using CoulombAtom.packetDensity_support 0 hr hz) hg x

lemma packetSmooth_support {r s : ℝ} (hr : 0 < r) {g : TFSpace → ℝ}
    (hsg : Function.support g ⊆ closedBall 0 s) :
    tsupport (packetSmooth r g) ⊆ closedBall 0 (r+s) :=
  convolution_tsupport_bound
    (fun z hz => by simpa only [sub_zero] using CoulombAtom.packetDensity_support 0 hr hz)
    (fun z hz => by simpa only [mem_closedBall_zero_iff] using hsg hz)

end Work_LipschitzMollifier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff NNReal Topology

lemma compact_continuous_bound {g : TFSpace → ℝ} (hg : Continuous g)
    (hcg : HasCompactSupport g) : ∃ B : ℝ, ∀ x, ‖g x‖ ≤ B := by
  obtain ⟨B,hB⟩ := hcg.isCompact.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max B 0,fun x => ?_⟩
  by_cases hx : x ∈ tsupport g
  · exact (hB x hx).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx,norm_zero]
    exact le_max_right _ _

lemma packetSmooth_tendsto {ε : ℕ → ℝ} (he : ∀ n, 0 < ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) {g : TFSpace → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (x : TFSpace) :
    Tendsto (fun n => packetSmooth (ε n) g x) atTop (𝓝 (g x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => packetSmooth_error (he n) hg x)
  simpa only [mul_zero] using hlim.const_mul (L:ℝ)

lemma packetSmooth_pair_tendsto (μ : Measure TFSpace) {f : TFSpace → ℝ}
    (hf : Integrable f μ) {ε : ℕ → ℝ} {r : ℝ}
    (he : ∀ n, 0 < ε n) (heb : ∀ n, ε n ≤ r) (hlim : Tendsto ε atTop (𝓝 0))
    {g : TFSpace → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g) (hcg : HasCompactSupport g) :
    Tendsto (fun n => ∫ x, packetSmooth (ε n) g x*f x ∂μ) atTop
      (𝓝 (∫ x, g x*f x ∂μ)) := by
  obtain ⟨B,hB⟩ := compact_continuous_bound hg.continuous hcg
  have hn (n : ℕ) (x : TFSpace) : ‖packetSmooth (ε n) g x‖ ≤ (L:ℝ)*r+B := by
    calc
      _ = ‖packetSmooth (ε n) g x-g x+g x‖ := by rw [sub_add_cancel]
      _ ≤ ‖packetSmooth (ε n) g x-g x‖+‖g x‖ := norm_add_le _ _
      _ ≤ (L:ℝ)*r+B := add_le_add ((packetSmooth_error (he n) hg x).trans
        (mul_le_mul_of_nonneg_left (heb n) L.coe_nonneg)) (hB x)
  apply tendsto_integral_of_dominated_convergence (fun x => ((L:ℝ)*r+B)*‖f x‖)
  · intro n
    exact ((packetSmooth_contDiff (he n) hg.continuous).continuous.aestronglyMeasurable).mul
      hf.aestronglyMeasurable
  · exact hf.norm.const_mul _
  · intro n
    exact Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hn n x) (norm_nonneg _)
  · exact Eventually.of_forall fun x => (packetSmooth_tendsto he hlim hg x).mul_const (f x)

end CoulombAnalysis

end

end OAI
