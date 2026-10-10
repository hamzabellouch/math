import Mathlib
import OAI.Analysis.MumfordShah.GradientProjection

namespace OAI

/-! MumfordShah cutoffs. -/

noncomputable section
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
namespace MumfordShah
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Set MeasureTheory Topology InnerProductSpace
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter
open scoped ENNReal ContDiff

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap

open Set MeasureTheory Metric Topology Filter
open scoped ContDiff

lemma compact_smooth_cutoff {A O : Set ℂ} (hA : IsCompact A)
    (hO : IsOpen O) (hAO : A ⊆ O) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ O ∧ (∀ x ∈ A, χ =ᶠ[𝓝 x] 1) ∧ ∀ x, χ x ∈ Icc (0:ℝ) 1 := by
  obtain ⟨R, hAR⟩ := hA.isBounded.subset_ball (0 : ℂ)
  obtain ⟨V, hV, hAV, hVO⟩ := hA.exists_isOpen_closure_subset
    ((hO.inter isOpen_ball).mem_nhdsSet.mpr (subset_inter hAO hAR))
  have hVc : IsCompact (closure V) := (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
    isClosed_closure (hVO.trans (inter_subset_right.trans ball_subset_closedBall))
  obtain ⟨W, hW, hAW, hWV⟩ := hA.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hAV)
  obtain ⟨χ, hχ, hχrange, hχsupp, hχone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (modelWithCornersSelf ℝ ℂ) (n := (⊤ : ℕ∞))
      hV isClosed_closure hWV
  have hts : tsupport χ = closure V := by rw [tsupport, hχsupp]
  refine ⟨χ, contMDiff_iff_contDiff.mp hχ, ?_, ?_, ?_, ?_⟩
  · simpa [HasCompactSupport, hts] using hVc
  · rw [hts]
    exact hVO.trans inter_subset_left
  · intro x hx
    filter_upwards [hW.mem_nhds (hAW hx)] with y hy
    exact (hχone y).mp (subset_closure hy)
  · intro x
    exact hχrange (mem_range_self x)

open Set MeasureTheory Topology InnerProductSpace
open scoped ENNReal ContDiff

instance : CompleteSpace compactGradientClosure := by
  unfold compactGradientClosure
  infer_instance

def scaledCutoff (χ : ℂ → ℝ) (r : ℝ) (x : ℂ) : ℝ := χ (r⁻¹ • x)

lemma scaledCutoff_smooth {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (r : ℝ) :
    ContDiff ℝ ∞ (scaledCutoff χ r) :=
  hχ.comp (contDiff_id.const_smul r⁻¹)

lemma scaledCutoff_fderiv {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (r : ℝ) (x : ℂ) :
    fderiv ℝ (scaledCutoff χ r) x =
      (fderiv ℝ χ (r⁻¹ • x)).comp (r⁻¹ • ContinuousLinearMap.id ℝ ℂ) := by
  exact ((hχ.differentiable (by norm_num) _).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul r⁻¹)).fderiv

lemma scaledCutoff_gradient_bound {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {M r : ℝ} (hr : 0 < r) (hM : ∀ x, ‖gradient χ x‖ ≤ M) (x : ℂ) :
    ‖gradient (scaledCutoff χ r) x‖ ≤ M / r := by
  have hb := (fderiv ℝ χ (r⁻¹ • x)).opNorm_comp_le (r⁻¹ • ContinuousLinearMap.id ℝ ℂ)
  have hc : ‖fderiv ℝ χ (r⁻¹ • x)‖ ≤ M := by simpa [gradient] using hM (r⁻¹ • x)
  calc
    ‖gradient (scaledCutoff χ r) x‖ = ‖fderiv ℝ (scaledCutoff χ r) x‖ := by simp [gradient]
    _ ≤ ‖fderiv ℝ χ (r⁻¹ • x)‖ * ‖r⁻¹ • ContinuousLinearMap.id ℝ ℂ‖ := by
      rw [scaledCutoff_fderiv hχ]; exact hb
    _ = ‖fderiv ℝ χ (r⁻¹ • x)‖ * r⁻¹ := by simp [norm_smul, abs_of_pos hr]
    _ ≤ M * r⁻¹ := mul_le_mul_of_nonneg_right hc (inv_nonneg.mpr hr.le)
    _ = M/r := by rw [div_eq_mul_inv]

theorem exists_scaled_cutoff_family :
    ∃ χ : ℂ → ℝ, ∃ M : ℝ, 0 ≤ M ∧ ContDiff ℝ ∞ χ ∧
      ∀ r : ℝ, 0 < r →
        HasCompactSupport (scaledCutoff χ r) ∧
        (∀ x, scaledCutoff χ r x ∈ Icc (0:ℝ) 1) ∧
        (∀ x, ‖x‖ ≤ r → scaledCutoff χ r x = 1) ∧
        (∀ x, ‖gradient (scaledCutoff χ r) x‖ ≤ M/r) ∧
        (∀ x, (‖x‖ ≤ r ∨ 2*r ≤ ‖x‖) → gradient (scaledCutoff χ r) x = 0) ∧
        tsupport (scaledCutoff χ r) ⊆ closedBall (0:ℂ) (2*r) := by
  obtain ⟨χ,hχ,hc,hs,h1,hrange⟩ := compact_smooth_cutoff
    (isCompact_closedBall (0:ℂ) 1) isOpen_ball (closedBall_subset_ball (by norm_num : (1:ℝ)<2))
  obtain ⟨M,hM⟩ := (compactSupport_gradient hc).exists_bound_of_continuous (continuous_gradient_of_smooth hχ)
  refine ⟨χ,M,(norm_nonneg (gradient χ 0)).trans (hM 0),hχ,?_⟩
  intro r hr
  have hnorm (x : ℂ) : ‖r⁻¹ • x‖ = ‖x‖/r := by simp [abs_of_pos hr, div_eq_mul_inv, mul_comm]
  have ht (x : ℂ) (hx : 2*r ≤ ‖x‖) : r⁻¹ • x ∉ tsupport χ := by
    intro h
    have : ‖r⁻¹ • x‖ < 2 := by simpa only [mem_ball, dist_zero_right] using hs h
    rw [hnorm] at this
    have := (div_lt_iff₀ hr).mp this
    linarith
  have hts : tsupport (scaledCutoff χ r) ⊆ closedBall (0:ℂ) (2*r) := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra h
    have hxge : 2*r ≤ ‖x‖ := by
      simpa only [mem_closedBall, dist_zero_right, not_le] using (le_of_lt (show 2*r < ‖x‖ by simpa [mem_closedBall, dist_zero_right] using h))
    have hz := image_eq_zero_of_notMem_tsupport (ht x hxge)
    exact hx hz
  refine ⟨(isCompact_closedBall (0:ℂ) (2*r)).of_isClosed_subset (isClosed_tsupport _) hts,
    fun x => hrange _, ?_, scaledCutoff_gradient_bound hχ hr hM, ?_, hts⟩
  · intro x hx
    have hi : r⁻¹ • x ∈ closedBall (0:ℂ) 1 := by
      simp only [mem_closedBall, dist_zero_right, hnorm]
      exact (div_le_iff₀ hr).mpr (by simpa using hx)
    exact (h1 _ hi).self_of_nhds
  · intro x hx
    have hz : fderiv ℝ χ (r⁻¹ • x) = 0 := by
      rcases hx with hx | hx
      · have hi : r⁻¹ • x ∈ closedBall (0:ℂ) 1 := by
          simp only [mem_closedBall, dist_zero_right, hnorm]
          exact (div_le_iff₀ hr).mpr (by simpa using hx)
        rw [Filter.EventuallyEq.fderiv_eq (h1 _ hi)]
        simp
      · exact fderiv_of_notMem_tsupport ℝ (ht x hx)
    rw [gradient, scaledCutoff_fderiv hχ, hz]
    simp

end MumfordShah
end

end OAI
