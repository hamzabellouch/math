import Mathlib
import OAI.Analysis.MumfordShah.EnergyLimits

namespace OAI

/-! MumfordShah projection pairing. -/

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
open Set MeasureTheory Topology InnerProductSpace
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Filter
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap

open Set MeasureTheory Metric Topology
open scoped ENNReal ContDiff

instance instCompleteSpaceCompactGradientClosureProjectionPairing :
    CompleteSpace compactGradientClosure := by
  unfold compactGradientClosure
  infer_instance

instance instCompleteSpaceCompactGradientClosureProjectionPairingAux :
    CompleteSpace compactGradientClosure := by
  unfold compactGradientClosure
  infer_instance

lemma local_memLp_add_right {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} {f : ℂ → E}
    (hf : ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → MemLp f p (volume.restrict U)) (t : ℂ) :
    ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → MemLp (fun x => f (x+t)) p (volume.restrict U) := by
  intro U hU hb
  let S := (fun x : ℂ => x-t) ⁻¹' U
  have hs : IsOpen S := hU.preimage (continuous_id.sub continuous_const)
  have heq : S = (fun x : ℂ => x+t) '' U := by
    ext x
    constructor
    · intro hx; exact ⟨x-t,hx,sub_add_cancel _ _⟩
    · rintro ⟨y,hy,rfl⟩; simpa [S] using hy
  have hsb : Bornology.IsBounded S := by
    rw [heq]
    exact (isometry_add_right t).lipschitzWith.isBounded_image hb
  have hd : (fun x : ℂ => x+t) ⁻¹' S = U := by ext x; simp [S]
  have hm := (measurePreserving_add_right (volume : Measure ℂ) t).restrict_preimage hs.measurableSet
  simpa only [hd,Function.comp_def] using (hf S hs hsb).comp_measurePreserving hm

lemma gradient_comp_add_right (ψ : ℂ → ℝ) (t x : ℂ) :
    gradient (fun y => ψ (y+t)) x = gradient ψ (x+t) := by
  simp only [gradient,fderiv_comp_add_right]

lemma divergence_free_add_right {G : ℂ → ℂ}
    (hdiv : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : ℂ, inner ℝ (G x) (gradient ψ x)) = 0) (t : ℂ) :
    ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : ℂ, inner ℝ (G (x+t)) (gradient ψ x)) = 0 := by
  intro ψ hψ hc
  have ht := hdiv (fun x => ψ (x+(-t))) (hψ.comp (contDiff_id.add contDiff_const))
    (hc.comp_homeomorph (Homeomorph.addRight (-t)))
  rw [← (measurePreserving_add_right (volume : Measure ℂ) t).integral_comp
    (Homeomorph.addRight t).measurableEmbedding (fun x => inner ℝ (G x) (gradient (fun x => ψ (x+(-t))) x))] at ht
  simpa only [gradient_comp_add_right,add_neg_cancel_right] using ht

lemma linear_growth_add_right {G : ℂ → ℂ}
    (hG : ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → MemLp G 2 (volume.restrict U))
    {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ R : ℝ, 1 ≤ R → (∫ x in ball (0:ℂ) R, ‖G x‖^2) ≤ C*(1+R)) (t : ℂ) :
    ∀ R : ℝ, 1 ≤ R → (∫ x in ball (0:ℂ) R, ‖G (x+t)‖^2) ≤ (C*(1+‖t‖))*(1+R) := by
  intro R hR
  rw [← (measurePreserving_add_right (volume : Measure ℂ) t).setIntegral_image_emb
    (Homeomorph.addRight t).measurableEmbedding (fun x => ‖G x‖^2) (ball 0 R)]
  have hsub : (fun x => x+t) '' ball (0:ℂ) R ⊆ ball 0 (R+‖t‖) := by
    rintro x ⟨y,hy,rfl⟩
    simp only [mem_ball,dist_zero_right] at hy ⊢
    exact (norm_add_le _ _).trans_lt (by linarith)
  have hin := (hG (ball 0 (R+‖t‖)) isOpen_ball isBounded_ball).integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hle := setIntegral_mono_set hin (ae_of_all _ (fun x => sq_nonneg ‖G x‖)) (Filter.Eventually.of_forall hsub)
  have hgr := hg (R+‖t‖) (by linarith [norm_nonneg t])
  calc
    _ ≤ ∫ x in ball (0:ℂ) (R+‖t‖), ‖G x‖^2 := hle
    _ ≤ C*(1+(R+‖t‖)) := hgr
    _ ≤ (C*(1+‖t‖))*(1+R) := by nlinarith [mul_nonneg hC (mul_nonneg (norm_nonneg t) (le_trans zero_le_one hR))]

theorem translated_projection_pairing_zero {φ : ℂ → ℝ} {w : PlaneL2} {G : ℂ → ℂ}
    (htest : CompactDivergenceTestable φ w)
    (hφ : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → MemLp φ 2 (volume.restrict S))
    (hG : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → MemLp G 2 (volume.restrict S))
    (hdiv : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : ℂ, inner ℝ (G x) (gradient ψ x)) = 0)
    {C D E R : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) (hR : 1 ≤ R)
    (hgrowth : ∀ T : ℝ, 1 ≤ T → (∫ x in ball (0:ℂ) T, ‖G x‖^2) ≤ C*(1+T))
    (hdecay : ∀ᵐ x ∂volume, R ≤ ‖x‖ → |φ x| ≤ D/‖x‖)
    (hwdecay : ∀ᵐ x ∂volume, R ≤ ‖x‖ → ‖w x‖ ≤ E/‖x‖^2) (t : ℂ) :
    (∫ x : ℂ, inner ℝ (G x) (w (x-t))) = 0 := by
  have ht := divergence_pairing_zero_of_decay htest hφ (local_memLp_add_right hG t)
    (divergence_free_add_right hdiv t) (mul_nonneg hC (by positivity)) hD hE hR
    (linear_growth_add_right hG hC hgrowth t) hdecay hwdecay
  rw [← (measurePreserving_add_right (volume : Measure ℂ) t).integral_comp
    (Homeomorph.addRight t).measurableEmbedding (fun x => inner ℝ (G x) (w (x-t)))]
  simpa only [add_sub_cancel_right] using ht

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap

end MumfordShah
end

end OAI
