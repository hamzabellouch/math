import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.ChartPairing
import OAI.Geometry.WeakMTW.Geodesics.GlobalFlow
import OAI.Geometry.WeakMTW.Coordinates.CoordinateEquation

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def geodesicFan (P : ℝ → TangentBundle (model n) M) (z : ℝ × ℝ) : TangentBundle (model n) M :=
   geodesicFlow z.1 (P z.2)

 def fanCoordinates (x : M) (P : ℝ → TangentBundle (model n) M) (z : ℝ × ℝ) : Model n × Model n :=
   stateChart x (geodesicFan P z)

 def fanDomain (x : M) (P : ℝ → TangentBundle (model n) M) : Set (ℝ × ℝ) :=
   (geodesicFan P) ⁻¹' (stateChart x).source

 def fanMomentum (P : ℝ → TangentBundle (model n) M) (t : ℝ) : ℝ :=
   inner ℝ (geodesicFlow t (P 0)).2
     (mfderiv 𝓘(ℝ, ℝ) (model n) (fun s => geodesic (P s) t) 0 (1 : ℝ))

 theorem geodesicFan_smooth {P : ℝ → TangentBundle (model n) M}
    (hP : ContMDiff 𝓘(ℝ, ℝ) ((model n).prod (model n)) ∞ P) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) ((model n).prod (model n)) ∞ (geodesicFan P) := by
   have ht : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞ Prod.fst :=
     contMDiff_iff_contDiff.mpr contDiff_fst
   have hs : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞ Prod.snd :=
     contMDiff_iff_contDiff.mpr contDiff_snd
   exact geodesicFlow_smooth.comp (ht.prodMk (hP.comp hs))

 theorem fanDomain_open (x : M) {P : ℝ → TangentBundle (model n) M}
    (hP : ContMDiff 𝓘(ℝ, ℝ) ((model n).prod (model n)) ∞ P) : IsOpen (fanDomain x P) :=
   (stateChart x).open_source.preimage (geodesicFan_smooth hP).continuous

 theorem fanCoordinates_smooth (x : M) {P : ℝ → TangentBundle (model n) M}
    (hP : ContMDiff 𝓘(ℝ, ℝ) ((model n).prod (model n)) ∞ P) :
    ContDiffOn ℝ ∞ (fanCoordinates x P) (fanDomain x P) := by
   have hd : ContMDiffOn ((model n).prod (model n)) 𝓘(ℝ, Model n × Model n) ∞
       (stateChart x) (stateChart (E := Model n) x).source :=
     contMDiffOn_extChartAt (I := (model n).prod (model n))
       (x := (⟨x,0⟩ : TangentBundle (model n) M))
   exact contMDiffOn_iff_contDiffOn.mp (hd.comp
     (geodesicFan_smooth hP).contMDiffOn (fun _ h => h))

 theorem fanCoordinates_ode (x : M) (P : ℝ → TangentBundle (model n) M)
    {z : ℝ × ℝ} (hz : z ∈ fanDomain x P) :
    (fanCoordinates x P z).1 ∈ (chartAt (Model n) x).target ∧
      HasDerivAt (fun t => fanCoordinates x P (t,z.2))
        (geodesicSpray (metric x) (fanCoordinates x P z)) z.1 := by
   have hm : geodesic (P z.2) z.1 ∈ (chartAt (Model n) x).source :=
     (stateChart_source x _).mp hz
   exact ⟨(chartAt (Model n) x).map_source hm, geodesic_coordinate_equation x (P z.2) z.1 hm⟩

 theorem fanCoordinates_energy (x : M) (P : ℝ → TangentBundle (model n) M)
    {z : ℝ × ℝ} (hz : z ∈ fanDomain x P) :
    metric x (fanCoordinates x P z).1 (fanCoordinates x P z).2 (fanCoordinates x P z).2 =
      ‖(P z.2).2‖ ^ 2 := by
   have hm : (geodesicFlow z.1 (P z.2)).1 ∈ (chartAt (Model n) x).source :=
     (stateChart_source x _).mp hz
   have hh := stateChart_pairing x (geodesicFlow z.1 (P z.2)).1 hm
     (geodesicFlow z.1 (P z.2)).2 (geodesicFlow z.1 (P z.2)).2
   change metric x (fanCoordinates x P z).1 (fanCoordinates x P z).2
     (fanCoordinates x P z).2 = _ at hh
   rw [hh, real_inner_self_eq_norm_sq, geodesicFlow_norm]

 theorem fanMomentum_coord (x : M) {P : ℝ → TangentBundle (model n) M}
    (hP : ContMDiff 𝓘(ℝ, ℝ) ((model n).prod (model n)) ∞ P) {t : ℝ}
    (ht : (t,0) ∈ fanDomain x P) :
    fanMomentum P t = metric x (fanCoordinates x P (t,0)).1
      (fanCoordinates x P (t,0)).2
      (fderiv ℝ (fun z => (fanCoordinates x P z).1) (t,0) (0,1)) := by
   have hq := ((fanCoordinates_smooth x hP _ ht).contDiffAt
     ((fanDomain_open x hP).mem_nhds ht)).differentiableAt (by simp)
   have hγ : ContMDiff 𝓘(ℝ, ℝ) (model n) ∞ (fun s => geodesic (P s) t) :=
     (contMDiff_proj (TangentSpace (model n))).comp
       ((geodesicFlow_smooth_fixed t).comp hP)
   have hm : geodesic (P 0) t ∈ (chartAt (Model n) x).source :=
     (stateChart_source x _).mp ht
   have hd := curveState_chart_deriv' x (hγ.mdifferentiable (by simp) 0) hm
   have hp := (FirstVariation.parameter_hasDerivAt hq.fst).deriv
   change deriv (fun s => (fanCoordinates x P (t,s)).1) 0 = _ at hp
   change deriv (fun s => (fanCoordinates x P (t,s)).1) 0 = _ at hd
   rw [← hp,hd]
   exact (stateChart_pairing x (geodesic (P 0) t) hm
     (geodesicFlow t (P 0)).2
     (mfderiv 𝓘(ℝ, ℝ) (model n) (fun s => geodesic (P s) t) 0 (1 : ℝ))).symm

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
