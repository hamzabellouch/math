import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.SprayProjection
import OAI.Analysis.BiholderTransport.Coordinates.IntrinsicGradient
import OAI.Analysis.BiholderTransport.Coordinates.CoordinatePairingDerivative

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

namespace WeakMTWTransport

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma sprayFlow_chart_hasDerivAt (a z : TangentBundle 𝓘(ℝ,E) M) {t : ℝ}
    (hz : (sprayFlow t z).1 ∈ (extChartAt 𝓘(ℝ,E) a.1).source) :
    HasDerivAt (fun r => extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a (sprayFlow r z))
      (coordinateGeodesicField (riemannianCoordinateMetric a.1)
        (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a (sprayFlow t z))) t := by
  have hsrc : sprayFlow t z ∈ (chartAt (ModelProd E E) a).source := by
    simpa only [extChartAt_source] using (tangent_chart_source_iff a (sprayFlow t z)).mpr hz
  have hD := (hasMFDerivAt_extChartAt (I := 𝓘(ℝ,E).prod 𝓘(ℝ,E)) hsrc).comp t
    (sprayFlow_curve z t)
  rw [hasMFDerivAt_iff_hasFDerivAt] at hD
  let L : ℝ →L[ℝ] E×E :=
    (tangentCoordChange (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (sprayFlow t z) a (sprayFlow t z)).comp
      ((1 : ℝ →L[ℝ] ℝ).smulRight (geodesicSpray (sprayFlow t z)))
  have hD' : HasFDerivAt (fun r => extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a (sprayFlow r z)) L t := by
    convert! hD using 1
    rw [mfderiv_chartAt_eq_tangentCoordChange hsrc]
    rfl
  have hd := hD'.hasDerivAt
  apply hd.congr_deriv
  change tangentCoordChange (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (sprayFlow t z) a (sprayFlow t z)
    ((1:ℝ) • geodesicSpray (sprayFlow t z)) = _
  rw [one_smul]
  exact geodesicSpray_coordinates a (sprayFlow t z) hz

omit [FiniteDimensional ℝ E] [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)] in
lemma contMDiff_fiber_line (x : M) (v w : TangentSpace 𝓘(ℝ,E) x) :
    ContMDiff 𝓘(ℝ,ℝ) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞
      (fun s : ℝ => (⟨x,v+s • w⟩ : TangentBundle 𝓘(ℝ,E) M)) := by
  intro s
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_const,?_⟩
  let e := trivializationAt E (fun y : M => TangentSpace 𝓘(ℝ,E) y) x
  let L : TangentSpace 𝓘(ℝ,E) x →L[ℝ] E := e.continuousLinearMapAt ℝ x
  have heq : (fun r : ℝ => (e (⟨x,v+r • w⟩ : TangentBundle 𝓘(ℝ,E) M)).2) =
      (fun r : ℝ => L (v+r • w)) := by
    funext r
    exact (e.continuousLinearMapAt_apply_of_mem ℝ (mem_baseSet_trivializationAt E _ x) _).symm
  change ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ (fun r : ℝ => (e ⟨x,v+r • w⟩).2) s
  rw [heq]
  exact (L.contDiff.comp (contDiff_const.add (contDiff_id.smul contDiff_const))).contDiffAt.contMDiffAt

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

local instance globalPairingNormedSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace

lemma spray_variation_pairing_hasDerivAt
    {ν : ℝ → TangentBundle 𝓘(ℝ,E) M}
    (hν : ContMDiff 𝓘(ℝ,ℝ) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞ ν)
    {s e : ℝ} (he : HasDerivAt (fun r => ‖(ν r).2‖^2) e s) (t : ℝ) :
    HasDerivAt (fun r => inner ℝ (sprayFlow r (ν s)).2
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun k => (sprayFlow r (ν k)).1) s 1)) (e/2) t := by
  let F : ℝ×ℝ → TangentBundle 𝓘(ℝ,E) M := fun z => sprayFlow z.1 (ν z.2)
  let a := F (t,s)
  let χ := extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a
  let c := extChartAt 𝓘(ℝ,E) a.1
  let g := riemannianCoordinateMetric (E := E) a.1
  let U := F ⁻¹' χ.source
  let A : ℝ×ℝ → E := fun z => (χ (F z)).1
  let V : ℝ×ℝ → E := fun z => (χ (F z)).2
  have hF : ContMDiff 𝓘(ℝ,ℝ×ℝ) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞ F :=
    contMDiff_sprayFlow.comp (contDiff_fst.contMDiff.prodMk (hν.comp contDiff_snd.contMDiff))
  have hU : IsOpen U := (isOpen_extChartAt_source (I := 𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).preimage hF.continuous
  have hts : (t,s) ∈ U := mem_extChartAt_source a
  have hχ : ContMDiffOn (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,E×E) ∞ χ χ.source := by
    simpa only [χ,extChartAt_source] using
      (contMDiffOn_extChartAt (I := 𝓘(ℝ,E).prod 𝓘(ℝ,E)) (n := ∞) (x := a))
  have hq : ContDiffOn ℝ ∞ (fun z => χ (F z)) U :=
    (hχ.comp hF.contMDiffOn (fun _ h => h)).contDiffOn
  have hbase (z : ℝ×ℝ) (hz : z ∈ U) : (F z).1 ∈ c.source :=
    (tangent_chart_source_iff a (F z)).mp hz
  have himg (z : ℝ×ℝ) (hz : z ∈ U) : A z ∈ c.target := c.map_source (hbase z hz)
  have hode (z : ℝ×ℝ) (hz : z ∈ U) :
      HasDerivAt (fun q => A (q,z.2)) (V z) z.1 ∧
      HasDerivAt (fun q => V (q,z.2)) (-coordinateChristoffel g (A z) (V z) (V z)) z.1 := by
    have hd := sprayFlow_chart_hasDerivAt a (ν z.2) (hbase z hz)
    exact ⟨(ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt z.1 hd,
      (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt z.1 hd⟩
  have henergy : HasDerivAt (fun r => g (A (t,r)) (V (t,r)) (V (t,r))) e s := by
    apply he.congr_of_eventuallyEq
    have hnear : ∀ᶠ r in 𝓝 s, (t,r) ∈ U :=
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hU.mem_nhds hts)
    filter_upwards [hnear] with r hr
    exact (coordinate_spray_energy a (F (t,r)) (hbase _ hr)).trans
      (congrArg (fun a : ℝ => a^2) (sprayFlow_speed t (ν r)))
  have hG := coordinate_pairing_hasDerivAt (isOpen_extChartAt_target a.1)
    (contDiffOn_riemannianCoordinateMetric a.1)
    (fun _ hz => riemannianCoordinateMetric_isInvertible hz)
    (fun _ _ => riemannianCoordinateMetric_symm _ _)
    hU hq.fst hq.snd himg hode hts henergy
  apply hG.congr_of_eventuallyEq
  have hnear : ∀ᶠ r in 𝓝 t, (r,s) ∈ U :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hU.mem_nhds hts)
  filter_upwards [hnear] with r hr
  have hp : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ (fun k => (F (r,k)).1) :=
    (Bundle.contMDiff_proj (fun x : M => TangentSpace 𝓘(ℝ,E) x)).comp
      (hF.comp (contMDiff_const.prodMk_space contMDiff_id))
  have hsrc : (F (r,s)).1 ∈ (chartAt E a.1).source := by
    simpa only [c,extChartAt_source] using hbase _ hr
  have hDc := (hasMFDerivAt_extChartAt (I := 𝓘(ℝ,E)) hsrc).comp s
    (hp.mdifferentiable (by simp) s).hasMFDerivAt
  rw [hasMFDerivAt_iff_hasFDerivAt] at hDc
  have hAr := hasDerivAt_slice_right ((hq.fst.contDiffAt (hU.mem_nhds hr)).differentiableAt (by simp))
  let L : ℝ →L[ℝ] E := (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c (F (r,s)).1).comp
    (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun k => (F (r,k)).1) s)
  have hDc' : HasFDerivAt (fun k => c (F (r,k)).1) L s := by convert! hDc using 1
  have hJ := hAr.unique hDc'.hasDerivAt
  change directionalDerivative A (0,1) (r,s) =
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c (F (r,s)).1)
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun k => (F (r,k)).1) s 1) at hJ
  have hvel : V (r,s) = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c (F (r,s)).1 (F (r,s)).2 := by
    rw [mfderiv_extChartAt_eq_tangentCoordChange (hbase _ hr)]
    rfl
  change inner ℝ (F (r,s)).2
    (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun k => (F (r,k)).1) s 1) =
      g (A (r,s)) (V (r,s)) (directionalDerivative A (0,1) (r,s))
  apply (coordinate_metric_chart_pairing (hbase _ hr) _ _).symm.trans
  convert! congrArg₂ (fun u v : E => g (A (r,s)) u v) hvel.symm hJ.symm using 1

end WeakMTWTransport

end

end OAI
