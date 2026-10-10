import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ActiveCompact
import OAI.Analysis.BiholderTransport.Regularity.ContDiffParametricSecant
import OAI.Analysis.BiholderTransport.Coordinates.CompactEventuallyFiberwise

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

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff

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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

section
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma moving_half_cost_secant {A : Type*} [TopologicalSpace A]
    {Y : A → M} {a : A} (hY : ContinuousAt Y a) {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p ∈ minimizingVectors x)
    (hya : Y a=riemannianExp x ((1/2:ℝ) • p))
    (h : TangentSpace 𝓘(ℝ,Model n) x) {K : ℝ} (hK : inner ℝ p h<K) :
    ∀ᶠ q : ℝ×A in 𝓝 (0,a), 0≤q.1 →
      -2*(cost (riemannianExp x (q.1 • h)) (Y q.2)-cost x (Y q.2))≤K*q.1 := by
  let y := riemannianExp x ((1/2:ℝ) • p)
  let d := extChartAt 𝓘(ℝ,Model n) y
  have hyS : y∈d.source := mem_extChartAt_source y
  have hyT : d y∈d.target := d.map_source hyS
  have hdy : d.symm (d y)=y := d.left_inv hyS
  have hID := contracted_minimizer_mem_injectivityDomain hp
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
  let F := fun q : Model n×ℝ => (2:ℝ)*cost (riemannianExp x (q.2 • h)) (d.symm q.1)
  have hA : ContMDiffAt 𝓘(ℝ,Model n×ℝ) 𝓘(ℝ,Model n) ∞
      (fun q : Model n×ℝ => riemannianExp x (q.2 • h)) (d y,0) :=
    (contMDiff_riemannianExp_fiber (n := n) x _).comp (d y,0)
      (contDiffAt_snd.smul contDiffAt_const).contMDiffAt
  have hB : ContMDiffAt 𝓘(ℝ,Model n×ℝ) 𝓘(ℝ,Model n) ∞
      (fun q : Model n×ℝ => d.symm q.1) (d y,0) :=
    ((contMDiffWithinAt_extChartAt_symm_target y hyT).contMDiffAt
      ((isOpen_extChartAt_target y).mem_nhds hyT)).comp (d y,0) contDiffAt_fst.contMDiffAt
  have hC := cost_contMDiffAt_of_injectivityDomain
    (⟨x,(1/2:ℝ) • p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hID
  have hC' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2)
      (riemannianExp x ((0:ℝ) • h),d.symm (d y)) := by
    simpa only [zero_smul,riemannianExp_zero,hdy] using hC
  have hF0 := hC'.comp (d y,0) (hA.prodMk hB)
  have hF : ContDiffAt ℝ ∞ F (d y,0) :=
    contDiffAt_const.mul hF0.contDiffAt
  have hD : HasDerivAt (fun r : ℝ => F (d y,r)) (-inner ℝ p h) 0 := by
    have hN : HasFDerivAt (normalCost x ((1/2:ℝ) • p))
        (innerSL ℝ (-((1/2:ℝ) • p))) ((id (0:ℝ)) • h) := by
      simpa only [id_eq,zero_smul] using normalCost_hasFDerivAt_zero hID
    have H := (hN.comp_hasDerivAt 0
      ((hasDerivAt_id (0:ℝ)).smul_const h)).const_mul (2:ℝ)
    apply H.congr_deriv (by
      simp only [innerSL_apply_apply,inner_neg_left,real_inner_smul_left,one_smul]
      ring) |>.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun r => by dsimp [F,normalCost,y]; rw [hdy])
  have hDF := hF.differentiableAt (by simp) |>.hasFDerivAt
  have hDs := hDF.comp_hasDerivAt 0 ((hasDerivAt_const (0:ℝ) (d y)).prodMk (hasDerivAt_id (0:ℝ)))
  have heD : fderiv ℝ F (d y,0) (0,1) = -inner ℝ p h := hDs.unique hD
  have H := contDiffAt_parametric_secant_lower
    (hF.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
    (K := -K) (by rw [heD]; linarith)
  have hySa : Y a∈d.source := hya.symm ▸ hyS
  have hcY : ContinuousAt (fun q : ℝ×A => Y q.2) (0,a) := hY.comp continuousAt_snd
  have hc : ContinuousAt (fun q : ℝ×A => (d (Y q.2),q.1)) (0,a) :=
    ((show ContinuousAt d (Y a) by rw [hya]; exact continuousAt_extChartAt y).comp (f := fun q : ℝ×A => Y q.2) (x := (0,a))
      hcY).prodMk continuousAt_fst
  have hc' : Tendsto (fun q : ℝ×A => (d (Y q.2),q.1)) (𝓝 (0,a)) (𝓝 (d y,0)) := by
    simpa only [hya] using hc.tendsto
  have hnear : ∀ᶠ q : ℝ×A in 𝓝 (0,a), Y q.2∈d.source :=
    hcY.preimage_mem_nhds ((isOpen_extChartAt_source y).mem_nhds hySa)
  filter_upwards [hc'.eventually H,hnear] with q hq hsrc ht
  have hh := hq ht
  dsimp only [F] at hh
  rw [d.left_inv hsrc,zero_smul,riemannianExp_zero] at hh
  linarith

end

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma active_directional_upper_support {v : M → ℝ} (hv : Continuous v) {x : M}
    (h : TangentSpace 𝓘(ℝ,Model n) x) {K : ℝ}
    (hK : ∀ p∈activeLogs (n := n) v x, inner ℝ p h<K) :
    ∀ᶠ t : ℝ in 𝓝 0, 0≤t →
      cTransform v (riemannianExp x (t • h))-cTransform v x≤K*t := by
  let Y := fun z : TangentBundle 𝓘(ℝ,Model n) M => riemannianExp z.1 ((1/2:ℝ) • z.2)
  have hY : Continuous Y := (contMDiff_riemannianExp (n := n) (M := M)).continuous.comp
    ((contMDiff_tangentScale (E := Model n) (M := M)).continuous.comp
      (continuous_const.prodMk continuous_id))
  have hg : ContinuousAt (fun t : ℝ => riemannianExp x (t • h)) 0 :=
    (continuous_riemannianExp x).continuousAt.comp (continuousAt_id.smul continuousAt_const)
  have H : ∀ᶠ t : ℝ in 𝓝 0, ∀ z : TangentBundle 𝓘(ℝ,Model n) M,
      z.2∈activeLogs (n := n) v z.1 → z.1=riemannianExp x (t • h) →
      (0≤t → -2*(cost (riemannianExp x (t • h)) (Y z)-cost x (Y z))≤K*t) := by
    apply compact_eventually_fiberwise (isCompact_total_activeLogs hv)
      (FiberBundle.continuous_proj _ _) hg
    rintro ⟨a,p⟩ hp he
    simp only [zero_smul,riemannianExp_zero] at he
    subst a
    exact moving_half_cost_secant hY.continuousAt hp.1 rfl h (hK p hp)
  filter_upwards [H] with t ht ht0
  obtain ⟨p,hp⟩ := nonempty_activeLogs (n := n) hv (riemannianExp x (t • h))
  have hh := ht ⟨riemannianExp x (t • h),p⟩ hp rfl ht0
  have hs := active_split_lower_support hv hp.1 hp.2
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num) x
  dsimp only [Y] at hh
  linarith

end WeakMTWTransport

end

end OAI
