import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.FanCoordinates
import OAI.Geometry.WeakMTW.Geodesics.EnergyFirstVariation

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

 theorem geodesicFan_smooth_on {P : ℝ → TangentBundle (model n) M} {S : Set ℝ}
    (hP : ContMDiffOn 𝓘(ℝ, ℝ) ((model n).prod (model n)) ∞ P S) :
    ContMDiffOn 𝓘(ℝ,ℝ × ℝ) ((model n).prod (model n)) ∞ (geodesicFan P) (Prod.snd ⁻¹' S) := by
  have ht : ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,ℝ) ∞ Prod.fst :=
    contMDiff_iff_contDiff.mpr contDiff_fst
  have hs : ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,ℝ) ∞ Prod.snd :=
    contMDiff_iff_contDiff.mpr contDiff_snd
  exact geodesicFlow_smooth.comp_contMDiffOn
    (ht.contMDiffOn.prodMk (hP.comp hs.contMDiffOn (fun _ hz => hz)))

 theorem localFanDomain_open (x : M) {P : ℝ → TangentBundle (model n) M} {S : Set ℝ}
    (hS : IsOpen S) (hP : ContMDiffOn 𝓘(ℝ,ℝ) ((model n).prod (model n)) ∞ P S) :
    IsOpen ((Prod.snd ⁻¹' S) ∩ fanDomain x P) :=
  (geodesicFan_smooth_on hP).continuousOn.isOpen_inter_preimage
    (hS.preimage continuous_snd) (stateChart x).open_source

 theorem fanCoordinates_smooth_on (x : M) {P : ℝ → TangentBundle (model n) M} {S : Set ℝ}
    (hP : ContMDiffOn 𝓘(ℝ,ℝ) ((model n).prod (model n)) ∞ P S) :
    ContDiffOn ℝ ∞ (fanCoordinates x P) ((Prod.snd ⁻¹' S) ∩ fanDomain x P) := by
  have hd : ContMDiffOn ((model n).prod (model n)) 𝓘(ℝ, Model n × Model n) ∞
      (stateChart x) (stateChart (E := Model n) x).source :=
    contMDiffOn_extChartAt (I := (model n).prod (model n))
      (x := (⟨x,0⟩ : TangentBundle (model n) M))
  exact contMDiffOn_iff_contDiffOn.mp (hd.comp
    ((geodesicFan_smooth_on hP).mono inter_subset_left) (fun _ hz => hz.2))

 theorem fanMomentum_coord_on (x : M) {P : ℝ → TangentBundle (model n) M} {S : Set ℝ}
    (hS : IsOpen S) (h₀ : (0 : ℝ) ∈ S)
    (hP : ContMDiffOn 𝓘(ℝ,ℝ) ((model n).prod (model n)) ∞ P S) {t : ℝ}
    (ht : (t,0) ∈ fanDomain x P) :
    fanMomentum P t = metric x (fanCoordinates x P (t,0)).1
      (fanCoordinates x P (t,0)).2
      (fderiv ℝ (fun z => (fanCoordinates x P z).1) (t,0) (0,1)) := by
  have hm₀ : (t,0) ∈ (Prod.snd ⁻¹' S) ∩ fanDomain x P := ⟨h₀,ht⟩
  have hq := ((fanCoordinates_smooth_on x hP _ hm₀).contDiffAt
    ((localFanDomain_open x hS hP).mem_nhds hm₀)).differentiableAt (by simp)
  have hγ : ContMDiffAt 𝓘(ℝ,ℝ) (model n) ∞ (fun s => geodesic (P s) t) 0 :=
     (contMDiff_proj (TangentSpace (model n)) (IB := model n) (n := ∞)).contMDiffAt.comp 0
      ((geodesicFlow_smooth_fixed t).contMDiffAt.comp 0 ((hP 0 h₀).contMDiffAt (hS.mem_nhds h₀)))
  have hm : geodesic (P 0) t ∈ (chartAt (Model n) x).source := (stateChart_source x _).mp ht
  have hd := curveState_chart_deriv' x (hγ.mdifferentiableAt (by simp)) hm
  have hp := (FirstVariation.parameter_hasDerivAt hq.fst).deriv
  change deriv (fun s => (fanCoordinates x P (t,s)).1) 0 = _ at hp
  change deriv (fun s => (fanCoordinates x P (t,s)).1) 0 = _ at hd
  rw [← hp,hd]
  exact (stateChart_pairing x (geodesic (P 0) t) hm
    (geodesicFlow t (P 0)).2
    (mfderiv 𝓘(ℝ,ℝ) (model n) (fun s => geodesic (P s) t) 0 (1 : ℝ))).symm

 theorem fanMomentum_hasDerivAt_on {P : ℝ → TangentBundle (model n) M} {S : Set ℝ}
    (hS : IsOpen S) (h₀ : (0 : ℝ) ∈ S)
    (hP : ContMDiffOn 𝓘(ℝ,ℝ) ((model n).prod (model n)) ∞ P S) (t : ℝ) :
    HasDerivAt (fanMomentum P) (deriv (fun s => ‖(P s).2‖^2) 0 / 2) t := by
  let x := geodesic (P 0) t
  let U := (Prod.snd ⁻¹' S) ∩ fanDomain x P
  let q := fanCoordinates x P
  let c : ℝ × ℝ → Model n := fun z => (q z).1
  let V : ℝ × ℝ → Model n := fun z => (q z).2
  have hU : IsOpen U := localFanDomain_open x hS hP
  have ht : (t,0) ∈ U := ⟨h₀,(stateChart_source x _).mpr (mem_chart_source (Model n) x)⟩
  have hq : ContDiffOn ℝ ∞ q U := fanCoordinates_smooth_on x hP
  have hc : ContDiffOn ℝ 2 c U := hq.fst.of_le
    (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hdq := ((hq _ ht).contDiffAt (hU.mem_nhds ht)).differentiableAt (by simp)
  have hdt := (fanCoordinates_ode x P ht.2).2
  have hm := (fanCoordinates_ode x P ht.2).1
  have hDG := ((metric_smooth x _ hm).contDiffAt
    ((chartAt (Model n) x).open_target.mem_nhds hm)).differentiableAt (by simp)
  have he : (fun s => metric x (c (t,s)) (V (t,s)) (V (t,s))) =ᶠ[𝓝 (0 : ℝ)]
      (fun s => ‖(P s).2‖^2) := by
    have hh : ∀ᶠ s in 𝓝 (0 : ℝ), (t,s) ∈ U :=
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hU.mem_nhds ht)
    filter_upwards [hh] with s hs
    exact fanCoordinates_energy x P hs.2
  have hpair := FirstVariation.energy_pairing_hasDerivAt (G := metric x) (c := c) (V := V) hU hc
    (fun z hz => (fanCoordinates_ode x P hz.2).2.fst) ht hdq.snd hDG
    (metric_symmetric x _) (fun v hv => metric_positive x hm hv) hdt.snd he
  apply hpair.congr_of_eventuallyEq
  have hh : ∀ᶠ r in 𝓝 t, (r,0) ∈ U :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hU.mem_nhds ht)
  filter_upwards [hh] with r hr
  exact fanMomentum_coord_on x hS h₀ hP hr.2

 theorem fanMomentum_affine_on {P : ℝ → TangentBundle (model n) M} {S : Set ℝ}
    (hS : IsOpen S) (h₀ : (0 : ℝ) ∈ S)
    (hP : ContMDiffOn 𝓘(ℝ,ℝ) ((model n).prod (model n)) ∞ P S) (t : ℝ) :
    fanMomentum P t = fanMomentum P 0 + t * (deriv (fun s => ‖(P s).2‖^2) 0 / 2) := by
  let K := deriv (fun s => ‖(P s).2‖^2) 0 / 2
  have hd : ∀ r : ℝ, HasDerivAt (fun r => fanMomentum P r-r*K) 0 r := by
    intro r
    have hh := (fanMomentum_hasDerivAt_on hS h₀ hP r).sub ((hasDerivAt_id r).mul_const K)
    change HasDerivAt (fun r => fanMomentum P r-r*K) (K-1*K) r at hh
    simpa only [one_mul,sub_self] using hh
  have hh := is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt) (fun r => (hd r).deriv) t 0
  simp only [zero_mul,sub_zero] at hh
  exact sub_eq_iff_eq_add.mp hh

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
