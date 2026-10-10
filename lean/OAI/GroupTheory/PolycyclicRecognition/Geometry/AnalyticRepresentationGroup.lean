import OAI.GroupTheory.PolycyclicRecognition.Geometry.AnalyticRepresentationAtlas

namespace OAI

/-! # Analytic group operations in representation coordinates -/

noncomputable section
namespace PolycyclicRecognition
open Set Filter
open scoped Manifold ContDiff Topology

variable {G E A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]
  {ρ : G →* Aˣ} (C : RepresentedLocalChart (E := E) ρ)

namespace RepresentedLocalChart

omit [IsTopologicalGroup G] in
theorem zero_mem_target : (0 : E) ∈ C.chart.target := by
  rw [← C.at_one]
  exact C.chart.map_source C.one_mem

omit [IsTopologicalGroup G] in
theorem symm_zero : C.chart.symm (0 : E) = 1 := by
  rw [← C.at_one]
  exact C.chart.left_inv C.one_mem

theorem contMDiff_mul : letI := C.chartedSpace;
    ContMDiff ((𝓘(ℝ,E)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) ω (fun p : G × G => p.1 * p.2) := by
  let cs : ChartedSpace E G := C.chartedSpace
  let ms : IsManifold (𝓘(ℝ,E)) ω G := C.isManifold
  have ht : C.chart.target ∈ 𝓝 (0 : E) := C.chart.open_target.mem_nhds C.zero_mem_target
  have hF : ContDiffAt ℝ ω C.realization 0 := C.realization_contDiff.contDiffAt ht
  have hc : ContinuousAt C.chart.symm (0 : E) := C.chart.continuousAt_symm C.zero_mem_target
  intro p
  rw [contMDiffAt_iff]
  refine ⟨continuous_mul.continuousAt, ?_⟩
  simp only [mfld_simps, Function.comp_def]
  have hchart (g : G) : chartAt E g = C.translated g := rfl
  have hrange : Set.range (Prod.map id id : E × E → E × E) = Set.univ := by
    ext x
    exact ⟨fun _ => Set.mem_univ _, fun _ => ⟨x,rfl⟩⟩
  simp only [hchart, hrange]
  change ContDiffWithinAt ℝ ω
    (fun q : E × E => (C.translated (p.1 * p.2))
      ((C.translated p.1).symm q.1 * (C.translated p.2).symm q.2)) Set.univ
    ((C.translated p.1) p.1, (C.translated p.2) p.2)
  simp only [translated_apply, translated_symm_apply, inv_mul_cancel, C.at_one]
  rw [contDiffWithinAt_univ]
  have hf : ContDiffAt ℝ ω (fun q : E × E => C.coordinate
      ((((ρ (p.1 * p.2))⁻¹ : Aˣ) : A) *
        (((ρ p.1 : A) * C.realization q.1) * ((ρ p.2 : A) * C.realization q.2)) - 1)) (0,0) :=
    C.coordinate.contDiff.contDiffAt.comp _
      ((contDiffAt_const.mul ((contDiffAt_const.mul (hF.comp (f := Prod.fst) (0,0) contDiffAt_fst)).mul
        (contDiffAt_const.mul (hF.comp (f := Prod.snd) (0,0) contDiffAt_snd)))).sub contDiffAt_const)
  apply hf.congr_of_eventuallyEq
  have hq1 : ∀ᶠ q : E × E in 𝓝 (0,0), q.1 ∈ C.chart.target :=
    continuousAt_fst.tendsto.eventually ht
  have hq2 : ∀ᶠ q : E × E in 𝓝 (0,0), q.2 ∈ C.chart.target :=
    continuousAt_snd.tendsto.eventually ht
  have hw : ContinuousAt (fun q : E × E => (p.1 * p.2)⁻¹ *
      ((p.1 * C.chart.symm q.1) * (p.2 * C.chart.symm q.2))) (0,0) :=
    continuousAt_const.mul ((continuousAt_const.mul (hc.comp (f := Prod.fst) continuousAt_fst)).mul
      (continuousAt_const.mul (hc.comp (f := Prod.snd) continuousAt_snd)))
  have hw0 : (p.1 * p.2)⁻¹ * ((p.1 * C.chart.symm 0) * (p.2 * C.chart.symm 0)) = 1 := by
    rw [C.symm_zero, mul_one, mul_one, inv_mul_cancel]
  have hws := hw.tendsto.eventually (hw0 ▸ C.chart.open_source.mem_nhds C.one_mem)
  filter_upwards [hq1,hq2,hws] with q hq1 hq2 hq
  rw [C.coordinate_eq _ hq]
  simp only [map_mul, map_inv, Units.val_mul]
  rw [← C.realization_eq q.1 hq1, ← C.realization_eq q.2 hq2]

theorem contMDiff_inv : letI := C.chartedSpace;
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) ω (fun g : G => g⁻¹) := by
  let cs : ChartedSpace E G := C.chartedSpace
  let ms : IsManifold (𝓘(ℝ,E)) ω G := C.isManifold
  have ht : C.chart.target ∈ 𝓝 (0 : E) := C.chart.open_target.mem_nhds C.zero_mem_target
  have hF : ContDiffAt ℝ ω C.inverseRealization 0 := C.inverseRealization_contDiff.contDiffAt ht
  have hc : ContinuousAt C.chart.symm (0 : E) := C.chart.continuousAt_symm C.zero_mem_target
  intro g
  rw [contMDiffAt_iff]
  refine ⟨continuous_inv.continuousAt, ?_⟩
  simp only [mfld_simps, Function.comp_def]
  have hchart (g : G) : chartAt E g = C.translated g := rfl
  simp only [hchart, translated_apply, translated_symm_apply, inv_mul_cancel, C.at_one]
  change ContDiffWithinAt ℝ ω
    (fun x : E => C.chart ((g⁻¹)⁻¹ * (g * C.chart.symm x)⁻¹)) Set.univ 0
  rw [contDiffWithinAt_univ]
  have hf : ContDiffAt ℝ ω (fun x : E => C.coordinate
      ((ρ g : A) * C.inverseRealization x * (((ρ g)⁻¹ : Aˣ) : A) - 1)) 0 :=
    C.coordinate.contDiff.contDiffAt.comp _
      (((contDiffAt_const.mul hF).mul contDiffAt_const).sub contDiffAt_const)
  apply hf.congr_of_eventuallyEq
  have hw : ContinuousAt (fun x : E => (g⁻¹)⁻¹ * (g * C.chart.symm x)⁻¹) 0 :=
    continuousAt_const.mul (continuousAt_const.mul hc).inv
  have hw0 : (g⁻¹)⁻¹ * (g * C.chart.symm 0)⁻¹ = 1 := by
    rw [C.symm_zero, mul_one, inv_inv, mul_inv_cancel]
  have hws := hw.tendsto.eventually (hw0 ▸ C.chart.open_source.mem_nhds C.one_mem)
  filter_upwards [ht,hws] with x hx hsource
  rw [C.coordinate_eq _ hsource, inv_inv, mul_inv_rev, map_mul, map_mul, map_inv,
    Units.val_mul, Units.val_mul, ← C.inverseRealization_eq x hx]
  simp only [map_inv, mul_assoc]

/-- These representation coordinates give an actual analytic Lie group. -/
theorem lieGroup : letI := C.chartedSpace; LieGroup (𝓘(ℝ,E)) ω G := by
  let cs : ChartedSpace E G := C.chartedSpace
  exact { C.isManifold with
    contMDiff_mul := C.contMDiff_mul
    contMDiff_inv := C.contMDiff_inv }

end RepresentedLocalChart
end PolycyclicRecognition

end

end OAI
