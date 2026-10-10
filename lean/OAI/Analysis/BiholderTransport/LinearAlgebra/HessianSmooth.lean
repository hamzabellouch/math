import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.TransverseConcavity
import OAI.Analysis.BiholderTransport.CostGeometry.CostSmooth
import OAI.Analysis.BiholderTransport.Regularity.ContDiffUncurryIterated

namespace OAI

noncomputable section

namespace WeakMTWTransport

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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

section
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma hessianValue_contDiffAt {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) (xi : TangentSpace 𝓘(ℝ,Model n) x) :
    ContDiffAt ℝ ∞ (fun v => hessianValue x v xi) p := by
  have exp_smooth := contMDiff_riemannianExp_fiber (n := n) x
  have hA : ContMDiffAt 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x × ℝ) 𝓘(ℝ,Model n) ∞
      (fun q : TangentSpace 𝓘(ℝ,Model n) x × ℝ => riemannianExp x (q.2 • xi)) (p,(0:ℝ)) :=
    (exp_smooth _).comp (p,(0:ℝ)) (contDiffAt_snd.smul contDiffAt_const).contMDiffAt
  have hB : ContMDiffAt 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x × ℝ) 𝓘(ℝ,Model n) ∞
      (fun q : TangentSpace 𝓘(ℝ,Model n) x × ℝ => riemannianExp x q.1) (p,(0:ℝ)) :=
    (exp_smooth _).comp (p,(0:ℝ)) contDiffAt_fst.contMDiffAt
  have hC := cost_contMDiffAt_of_injectivityDomain (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp
  have hC' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x ((0:ℝ) • xi),riemannianExp x p) := by
    simpa only [zero_smul,riemannianExp_zero] using hC
  have hF : ContDiffAt ℝ ∞ (Function.uncurry
      (fun v : TangentSpace 𝓘(ℝ,Model n) x => fun t : ℝ =>
        cost (riemannianExp x (t • xi)) (riemannianExp x v))) (p,(0:ℝ)) :=
    by
      have H := (hC'.comp (p,(0:ℝ)) (hA.prodMk hB)).contDiffAt
      apply H.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall (fun _ => rfl)
  exact contDiffAt_iteratedDeriv_parameter hF 2

lemma WeakMTW.transverse_concaveOn_injectivityDomain
    (hmtw : WeakMTW (n := n) (M := M))
    (x : M) (p xi eta : TangentSpace 𝓘(ℝ,Model n) x)
    {D : Set ℝ} (hD : Convex ℝ D)
    (hline : ∀ s ∈ D, p + s • eta ∈ injectivityDomain x)
    (hortho : inner ℝ xi eta = 0) :
    ConcaveOn ℝ D (fun t : ℝ => hessianValue x (p+t • eta) xi) := by
  have hsmooth : ∀ s ∈ D, ContDiffAt ℝ ∞ (fun t : ℝ => hessianValue x (p+t • eta) xi) s := by
    intro s hs
    exact (hessianValue_contDiffAt (hline s hs) xi).comp s
      (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  apply hmtw.transverse_concaveOn x p xi eta hD
    (fun s hs => hline s (interior_subset hs)) hortho
  · intro s hs
    exact (hsmooth s hs).continuousAt.continuousWithinAt
  · intro s hs
    exact ((hsmooth s (interior_subset hs)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffWithinAt

end

open Set Filter
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma iteratedDeriv_two_affine_line {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (v : E) :
    iteratedDeriv 2 (fun t : ℝ => f (x+t • v)) 0 =
      fderiv ℝ (fderiv ℝ f) x v v := by
  let L : ℝ → E := fun t => x+t • v
  have hL (t : ℝ) : HasDerivAt L v t := by
    convert! (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const v) using 1
    simp
  have hL0 : L 0=x := by simp [L]
  have hLc : ContDiffAt ℝ 2 L 0 := contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
  have hL2 : iteratedDeriv 2 L 0=0 := by
    rw [iteratedDeriv_succ,iteratedDeriv_one]
    have heq : deriv L=fun _ => v := funext (fun t => (hL t).deriv)
    rw [heq,deriv_const]
  have hf' : ContDiffAt ℝ 2 f (L 0) := by rwa [hL0]
  have H := iteratedDeriv_vcomp_two hf' hLc
  simpa only [Function.comp_def,hL0,(hL 0).deriv,hL2,map_zero,add_zero,
    iteratedFDeriv_two_apply] using H

lemma directional_fderiv_hasDerivAt {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (v w : E) :
    HasDerivAt (fun t : ℝ => fderiv ℝ f (x+t • v) w)
      (fderiv ℝ (fderiv ℝ f) x v w) 0 := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hline : HasDerivAt (fun t : ℝ => x+t • v) v 0 := by
    convert! (hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const v) using 1
    simp
  have hd' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (x+(0:ℝ) • v) := by
    simpa only [zero_smul,add_zero] using hdf.hasFDerivAt
  have hd := (hd'.comp_hasDerivAt (f := fun t : ℝ => x+t • v) 0 hline).clm_apply (hasDerivAt_const 0 w)
  convert! hd using 1
  simp

lemma positive_schur_test {a b q A : ℝ} (hq : 0<q)
    (ht : ∀ t : ℝ, A ≤ a+2*t*b+t^2*q) : A ≤ a-b^2/q := by
  have H := ht (-b/q)
  have heq : a+2*(-b/q)*b+(-b/q)^2*q=a-b^2/q := by field_simp; ring
  rwa [heq] at H

lemma nonzero_pairing_positive_test {a b q A : ℝ} (hq : 0≤q) (hb : b≠0)
    (ht : ∀ t : ℝ, A≤a+2*t*b+t^2*q) : 0<q := by
  by_contra hn
  have h0 : q=0 := le_antisymm (le_of_not_gt hn) hq
  have H := ht ((A-a-1)/(2*b))
  rw [h0,mul_zero,add_zero] at H
  have he : a+2*((A-a-1)/(2*b))*b=A-1 := by field_simp; ring
  rw [he] at H
  linarith

end WeakMTWTransport

end

end OAI
