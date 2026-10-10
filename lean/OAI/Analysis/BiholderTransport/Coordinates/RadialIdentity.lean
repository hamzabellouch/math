import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.CostGradient
import OAI.Analysis.BiholderTransport.LinearAlgebra.HessianSmooth

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

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def normalCost (x : M) (p u : TangentSpace 𝓘(ℝ,Model n) x) : ℝ :=
  cost (riemannianExp x u) (riemannianExp x p)

lemma normalCost_contDiffAt {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) : ContDiffAt ℝ ∞ (normalCost x p) 0 := by
  have hc := cost_contMDiffAt_of_injectivityDomain (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp
  have hc' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x (0 : TangentSpace 𝓘(ℝ,Model n) x),riemannianExp x p) := by
    simpa only [riemannianExp_zero] using hc
  exact (hc'.comp 0 ((contMDiff_riemannianExp_fiber x 0).prodMk contMDiffAt_const)).contDiffAt

lemma shifted_exp_endpoint (x : M) (p : TangentSpace 𝓘(ℝ,Model n) x) (t : ℝ) :
    riemannianExp (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1
      ((1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2) = riemannianExp x p := by
  rw [riemannianExp_eq_sprayFlow]
  change (sprayFlow 1 (tangentScale (1-t) (sprayFlow t ⟨x,p⟩))).1 = _
  rw [sprayFlow_scale,mul_one,←sprayFlow_add,sub_add_cancel]
  exact (riemannianExp_eq_sprayFlow x p).symm

lemma shifted_injectivityDomain_near_zero {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) : ∀ᶠ t : ℝ in 𝓝 0,
    (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 := by
  let Z : ℝ → TangentBundle 𝓘(ℝ,Model n) M := fun t => tangentScale (1-t) (sprayFlow t ⟨x,p⟩)
  have hZ : ContMDiff 𝓘(ℝ,ℝ) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ Z :=
    contMDiff_tangentScale.comp ((contMDiff_const.sub contMDiff_id).prodMk
      (contMDiff_sprayFlow.comp (contMDiff_id.prodMk contMDiff_const)))
  have hZ0 : Z 0=⟨x,p⟩ := by
    dsimp [Z]
    rw [sprayFlow_zero]
    simp [tangentScale]
  have hh : Z 0 ∈ {z : TangentBundle 𝓘(ℝ,Model n) M | z.2 ∈ injectivityDomain z.1} := by
    rw [hZ0]; exact hp
  exact hZ.continuous.continuousAt.preimage_mem_nhds (isOpen_total_injectivityDomain.mem_nhds hh)

lemma normalCost_radial_fderiv_of_shift {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (xi : TangentSpace 𝓘(ℝ,Model n) x) {t : ℝ} (ht : t ≠ 0) (ht1 : t ≠ 1)
    (hp : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (hf : DifferentiableAt ℝ (normalCost x p) (t • p)) :
    fderiv ℝ (normalCost x p) (t • p) xi = (t-1)*inner ℝ p xi := by
  have hD := cost_start_gradient_of_injectivityDomain hp
  rw [shifted_exp_endpoint] at hD
  have hD' : HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ)
      (fun b => dist b (riemannianExp x p)^2/2)
      (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1
      (innerSL ℝ ((-(1-t)) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2)) := by
    simpa only [cost,neg_smul] using hD
  have he : 1-t ≠ 0 := sub_ne_zero.mpr ht1.symm
  have H := spray_action_line_stationary x p xi t (1-t) he (riemannianExp x p) hD'
  have hv : HasDerivAt (fun s : ℝ => t • (p+s • xi)) (t • xi) 0 := by
    convert! (((hasDerivAt_const (0:ℝ) p).add ((hasDerivAt_id (0:ℝ)).smul_const xi)).const_smul t) using 1
    simp
  have hf' : HasFDerivAt (normalCost x p) (fderiv ℝ (normalCost x p) (t • p)) (t • (p+(0:ℝ) • xi)) := by
    simpa only [zero_smul,add_zero] using hf.hasFDerivAt
  have hfc := hf'.comp_hasDerivAt 0 hv
  have hn : HasDerivAt (fun s : ℝ => t*‖p+s • xi‖^2/2) (t*inner ℝ p xi) 0 := by
    convert! (((hasDerivAt_const (0:ℝ) p).add ((hasDerivAt_id (0:ℝ)).smul_const xi)).norm_sq.const_mul t).div_const 2 using 1
    simp
    ring
  have HH := hn.add (hfc.div_const (1-t))
  have hh : (t*inner ℝ p xi)+fderiv ℝ (normalCost x p) (t • p) (t • xi)/(1-t)=0 := by
    apply HH.unique
    convert! H using 1
    funext s
    simp only [normalCost,cost,riemannianExp_smul,Function.comp_def]
    rfl
  rw [map_smul,smul_eq_mul] at hh
  field_simp at hh
  have hh' : t * (fderiv ℝ (normalCost x p) (t • p) xi - (t-1)*inner ℝ p xi)=0 := by nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh').resolve_left ht)

lemma normalCost_radial_fderiv_near_zero {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) (xi : TangentSpace 𝓘(ℝ,Model n) x) :
    (fun t : ℝ => fderiv ℝ (normalCost x p) (t • p) xi) =ᶠ[𝓝 0]
      (fun t : ℝ => (t-1)*inner ℝ p xi) := by
  have hf := normalCost_contDiffAt hp
  have hline : ContDiffAt ℝ ∞ (fun t : ℝ => t • p) 0 := contDiffAt_id.smul contDiffAt_const
  have hline0 : (0:ℝ) • p=0 := zero_smul ℝ p
  have hfnear : ∀ᶠ t : ℝ in 𝓝 0, DifferentiableAt ℝ (normalCost x p) (t • p) := by
    have hh : ∀ᶠ u in 𝓝 (0 : TangentSpace 𝓘(ℝ,Model n) x), ContDiffAt ℝ 1 (normalCost x p) u :=
      (hf.of_le (m := 1) (by simp)).eventually (by norm_num)
    have ht : Tendsto (fun t : ℝ => t • p) (𝓝 0) (𝓝 0) := by
      simpa only [ContinuousAt,hline0] using hline.continuousAt
    exact (ht.eventually hh).mono (fun _ h => h.differentiableAt (by norm_num))
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, t≠0 →
      fderiv ℝ (normalCost x p) (t • p) xi=(t-1)*inner ℝ p xi := by
    filter_upwards [shifted_injectivityDomain_near_zero hp,hfnear,
      eventually_ne_nhds (show (0:ℝ)≠1 by norm_num)] with t ht hft ht1
    exact fun htn => normalCost_radial_fderiv_of_shift xi htn ht1 ht hft
  have hleft : ContinuousAt (fun t : ℝ => fderiv ℝ (normalCost x p) (t • p) xi) 0 := by
    have hdf := (hf.fderiv_right (m := ∞) (by simp)).continuousAt
    have hdf' : ContinuousAt (fderiv ℝ (normalCost x p)) ((0:ℝ) • p) := by rwa [hline0]
    exact (ContinuousAt.comp (f := fun t : ℝ => t • p) hdf' hline.continuousAt).clm_apply continuousAt_const
  have hright : ContinuousAt (fun t : ℝ => (t-1)*inner ℝ p xi) 0 := by fun_prop
  have heqpunct : (fun t : ℝ => fderiv ℝ (normalCost x p) (t • p) xi) =ᶠ[𝓝[≠] 0]
      (fun t : ℝ => (t-1)*inner ℝ p xi) := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht htn
    exact ht htn
  have heq0 := tendsto_nhds_unique_of_eventuallyEq
    (hleft.mono_left nhdsWithin_le_nhds) (hright.mono_left nhdsWithin_le_nhds) heqpunct
  filter_upwards [hnear] with t ht
  by_cases ht0 : t=0
  · simpa only [ht0] using heq0
  · exact ht ht0

lemma normalCost_radial_hessian {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) (xi : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (normalCost x p)) 0 p xi = inner ℝ p xi := by
  have hf := (normalCost_contDiffAt hp).of_le (m := 2)
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hd0 : HasDerivAt (fun t : ℝ => fderiv ℝ (normalCost x p) (t • p) xi)
      (fderiv ℝ (fderiv ℝ (normalCost x p)) 0 p xi) 0 := by
    simpa only [zero_add] using directional_fderiv_hasDerivAt hf p xi
  have heq := normalCost_radial_fderiv_near_zero hp xi
  have hright : HasDerivAt (fun t : ℝ => (t-1)*inner ℝ p xi) (inner ℝ p xi) 0 := by
    convert! ((hasDerivAt_id (0:ℝ)).sub_const 1).mul_const (inner ℝ p xi) using 1; simp only [one_mul]
  exact hd0.unique (hright.congr_of_eventuallyEq heq)

end WeakMTWTransport

end

end OAI
