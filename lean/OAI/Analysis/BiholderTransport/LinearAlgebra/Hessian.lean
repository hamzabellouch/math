import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.LocalMinSecondDeriv

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma localMin_hessian_nonneg {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hm : IsLocalMin f x) (v : E) :
    0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  let L : ℝ → E := fun t => x+t • v
  have hL (t : ℝ) : HasDerivAt L v t := by
    convert! (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const v) using 1
    simp
  have hL0 : L 0 = x := by simp [L]
  have hcont : ContinuousAt (fun t => f (L t)) 0 := by
    apply ContinuousAt.comp _ (hL 0).continuousAt
    simpa only [hL0] using hf.continuousAt
  have hmin : IsLocalMin (fun t => f (L t)) 0 :=
    (show IsLocalMin f (L 0) by rwa [hL0]).comp_continuous (hL 0).continuousAt
  have heq : deriv (fun t => f (L t)) =ᶠ[𝓝 (0:ℝ)]
      fun t => fderiv ℝ f (L t) v := by
    have hnear : ∀ᶠ t in 𝓝 (0:ℝ), ContDiffAt ℝ 2 f (L t) := by
      apply (show Tendsto L (𝓝 0) (𝓝 x) by simpa only [ContinuousAt,hL0] using (hL 0).continuousAt).eventually
      exact hf.eventually (by norm_num)
    filter_upwards [hnear] with t ht
    exact ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hL t)).deriv
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd : HasDerivAt (fun t => fderiv ℝ f (L t) v)
      (fderiv ℝ (fderiv ℝ f) x v v) 0 := by
    have hfd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (L 0) := by
      rw [hL0]; exact hdf.hasFDerivAt
    have hd0 := (hfd.comp_hasDerivAt 0 (hL 0)).clm_apply (hasDerivAt_const 0 v)
    convert! hd0 using 1
    simp
  have hh := localMin_second_deriv_nonneg hmin hcont
  rwa [heq.deriv_eq,hd.deriv] at hh

lemma symmetric_nonneg_bilinear_null {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hs : ∀ u v, B u v = B v u) (hp : ∀ u, 0 ≤ B u u)
    {v : E} (hv : B v v = 0) (w : E) : B v w = 0 := by
  let f : ℝ → ℝ := fun t => B (v+t • w) (v+t • w)
  have hmin : IsLocalMin f 0 := by
    filter_upwards [] with t
    simpa only [f,zero_smul,add_zero,hv] using hp (v+t • w)
  have heq : f = fun t => 2*t*(B v w)+t^2*(B w w) := by
    funext t
    simp only [f,map_add,map_smul,add_apply,smul_apply,smul_eq_mul,hv,hs w v]
    ring
  have hd : HasDerivAt f (2*B v w) 0 := by
    rw [heq]
    convert! (((hasDerivAt_id (0:ℝ)).const_mul 2).mul_const (B v w)).add
      (((hasDerivAt_id (0:ℝ)).pow 2).mul_const (B w w)) using 1
    norm_num
  have hh := hmin.hasDerivAt_eq_zero hd
  linarith

lemma localMin_hessian_null {f : E → ℝ} {x v : E}
    (hf : ContDiffAt ℝ 2 f x) (hm : IsLocalMin f x)
    (hv : fderiv ℝ (fderiv ℝ f) x v v = 0) (w : E) :
    fderiv ℝ (fderiv ℝ f) x v w = 0 := by
  exact symmetric_nonneg_bilinear_null
    (hf.isSymmSndFDerivAt (by simp)).eq (localMin_hessian_nonneg hf hm) hv w

end WeakMTWTransport

end

end OAI
