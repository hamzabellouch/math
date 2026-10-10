import Mathlib
import OAI.Analysis.SymmetricDomains.GeneratorPushForwardLinear
import OAI.Analysis.SymmetricDomains.OneParameterFderivDeriv

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hbd : Bornology.IsBounded U)
    (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
include hU hbd ha ha0 ham

theorem pushForwardGenerator_hasDerivAt_zero
    (Y : Affine n → Affine n) (hY : AnalyticOnNhd ℂ Y U)
    (x : Affine n) (hx : x∈U) :
    HasDerivAt (fun t : ℝ => pushForwardGenerator (a t) Y x)
      (-VectorField.lieBracket ℂ (infinitesimalGenerator a) Y x) 0 := by
  let X := infinitesimalGenerator a
  let y : ℝ → Affine n := fun t => (a (-t)).ambientAut x
  let A : ℝ → Affine n →L[ℂ] Affine n := fun t => fderiv ℂ (a (-t)).ambientAut x
  let B : ℝ → Affine n →L[ℂ] Affine n := fun t => fderiv ℂ (a t).ambientAut (y t)
  have hneg (t : ℝ) : a (-t)=(a t)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← ham,neg_add_cancel,ha0]
  have hy0 : y 0=x := by simp [y,ha0,ambientAut_apply (1 : Biholomorph U U) ⟨x,hx⟩]
  have hA0 : A 0=1 := by
    simpa only [A,neg_zero,ha0,derivativeAt] using derivativeAt_one hU (⟨x,hx⟩ : U)
  have hB0 : B 0=1 := by simpa only [B,hy0,ha0,derivativeAt] using derivativeAt_one hU (⟨x,hx⟩ : U)
  have hdy : HasDerivAt y (-X x) 0 := by
    have hh : HasDerivAt (fun t => (a t).ambientAut x) (X x) (-(0:ℝ)) := by
      simpa only [neg_zero] using infinitesimalGenerator_hasDerivAt hU hbd a ha ha0 ham x
    have ht := hh.scomp 0 ((hasDerivAt_id (0:ℝ)).neg)
    simpa only [Function.comp_def,neg_zero,neg_smul,one_smul] using ht
  have hdA : HasDerivAt A (-fderiv ℂ X x) 0 := by
    have hh : HasDerivAt (fun t => fderiv ℂ (a t).ambientAut x) (fderiv ℂ X x) (-(0:ℝ)) := by
      simpa only [neg_zero] using oneParameter_fderiv_hasDerivAt_zero hU hbd a ha ha0 ham x hx
    have ht := hh.scomp 0 ((hasDerivAt_id (0:ℝ)).neg)
    simpa only [Function.comp_def,neg_zero,neg_smul,one_smul] using ht
  have hdY : HasDerivAt (fun t => Y (y t)) (-(fderiv ℂ Y x) (X x)) 0 := by
    have hcomp := (((hY x hx).differentiableAt.hasFDerivAt).restrictScalars ℝ)
    rw [← hy0] at hcomp
    have ht := hcomp.comp_hasDerivAt 0 hdy
    change HasDerivAt (fun t => Y (y t)) ((fderiv ℂ Y (y 0)) (-X x)) 0 at ht
    simpa only [hy0,map_neg] using ht
  have hdAY : HasDerivAt (fun t => A t (Y x)) (-(fderiv ℂ X x) (Y x)) 0 := by
    have hl := ((ContinuousLinearMap.apply ℂ (Affine n) (Y x)).restrictScalars ℝ).hasFDerivAt (x := A 0)
    have ht := hl.comp_hasDerivAt 0 hdA
    exact ht
  let r : ℝ → Affine n := fun t => Y (y t)-A t (Y x)
  have hr0 : r 0=0 := by simp [r,hy0,hA0]
  have hdr : HasDerivAt r (-VectorField.lieBracket ℂ X Y x) 0 := by
    have ht := hdY.sub hdAY
    have heq : -(fderiv ℂ Y x) (X x) - (-(fderiv ℂ X x) (Y x)) =
        -VectorField.lieBracket ℂ X Y x := by
      dsimp only [VectorField.lieBracket]
      abel
    rw [heq] at ht
    exact ht
  have hB : ContinuousAt B 0 := by
    have ht := (ambientAut_derivative_joint_continuousAt hU (q := (a 0,y 0)) (hy0 ▸ hx)).comp (f := fun t : ℝ => (a t,y t)) (x := (0:ℝ))
      (ha.continuousAt.prodMk hdy.continuousAt)
    exact ht
  have he (t : ℝ) : B t (A t (Y x))=Y x := by
    have hprod := derivativeAt_mul hU (a t) (a (-t)) (⟨x,hx⟩ : U)
    rw [hneg,mul_inv_cancel,derivativeAt_one hU] at hprod
    have hh := congrArg (fun L : Affine n →L[ℂ] Affine n => L (Y x)) hprod
    change Y x = (fderiv ℂ (a t).ambientAut ((a t)⁻¹.toHomeomorph ⟨x,hx⟩).val)
      (fderiv ℂ (a t)⁻¹.ambientAut x (Y x)) at hh
    simpa only [B,A,y,hneg,ambientAut_apply (a t)⁻¹ ⟨x,hx⟩] using hh.symm
  have hp (t : ℝ) : pushForwardGenerator (a t) Y x=B t (Y (y t)) := by
    rw [pushForwardGenerator,dite_eq_left hx]
    dsimp only [B,y]
    rw [hneg,ambientAut_apply (a t)⁻¹ ⟨x,hx⟩]
    rfl
  have hp0 : pushForwardGenerator (a 0) Y x=Y x := by rw [hp,hB0,hy0]; rfl
  rw [hasDerivAt_iff_tendsto_slope]
  have hc : Tendsto (fun t : ℝ => B t (slope r 0 t)) (𝓝[≠] 0)
      (𝓝 (-VectorField.lieBracket ℂ X Y x)) := by
    have hbt : Tendsto B (𝓝[≠] (0:ℝ)) (𝓝 (B 0)) := hB.tendsto.mono_left nhdsWithin_le_nhds
    have heval : Continuous (fun p : (Affine n →L[ℂ] Affine n) × Affine n => p.1 p.2) :=
      continuous_fst.clm_apply continuous_snd
    have ht := heval.continuousAt.tendsto.comp (hbt.prodMk_nhds hdr.tendsto_slope)
    rw [hB0] at ht
    change Tendsto (fun t : ℝ => B t (slope r 0 t)) (𝓝[≠] 0)
      (𝓝 ((1 : Affine n →L[ℂ] Affine n) (-VectorField.lieBracket ℂ X Y x))) at ht
    exact ht
  apply hc.congr'
  filter_upwards [] with t
  rw [slope_def_module,slope_def_module,sub_zero,hr0,sub_zero,hp0,hp]
  dsimp only [r]
  rw [ContinuousLinearMap.map_smul_of_tower,map_sub,he]
end Biholomorph
end Release061

end

end OAI
