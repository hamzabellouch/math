import Mathlib
import OAI.Analysis.SymmetricDomains.ChartDensityMeasureLeft
import OAI.Analysis.SymmetricDomains.LocalHaarEqualMass

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
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]

omit [Group G] [IsTopologicalGroup G] [NormedSpace ℝ E] in

theorem chart_inverse_image_measurable (e : OpenPartialHomeomorph G E)
    {A : Set E} (hA : MeasurableSet A) (hAt : A⊆e.target) :
    MeasurableSet (e.symm '' A) := by
  classical
  let F : G → E := e.source.piecewise e (fun _ => 0)
  have hF : Measurable F := e.continuousOn_toFun.measurable_piecewise
    continuous_const.continuousOn e.open_source.measurableSet
  have heq : e.symm '' A = e.source ∩ F ⁻¹' A := by
    ext g
    constructor
    · rintro ⟨x,hx,rfl⟩
      have ht := hAt hx
      refine ⟨e.map_target ht,?_⟩
      simpa only [mem_preimage,F,piecewise_eq_of_mem _ _ _ (e.map_target ht),e.right_inv ht]
        using hx
    · rintro ⟨hg,ha⟩
      refine ⟨e g,?_,e.left_inv hg⟩
      simpa only [mem_preimage,F,piecewise_eq_of_mem _ _ _ hg] using ha
  rw [heq]
  exact e.open_source.measurableSet.inter (hA.preimage hF)

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem chartPart_inverse_image (e : OpenPartialHomeomorph G E)
    {A : Set E} (hAt : A⊆e.target) : chartPart e (e.symm '' A)=A := by
  ext x
  rw [mem_chartPart_iff]
  constructor
  · rintro ⟨hx,y,hy,heq⟩
    have : y=x := e.symm.injOn (hAt hy) hx heq
    simpa only [this] using hy
  · intro hx
    exact ⟨hAt hx,x,hx,rfl⟩

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem chartPart_map_inverse_image (e : OpenPartialHomeomorph G E)
    (F : G → G) {A : Set E} (_hAt : A⊆e.target)
    (hFs : ∀ x∈A, F (e.symm x)∈e.source) :
    chartPart e (F '' (e.symm '' A)) = (fun x => e (F (e.symm x))) '' A := by
  ext y
  rw [mem_chartPart_iff]
  constructor
  · rintro ⟨hy,g,⟨x,hx,rfl⟩,hxy⟩
    exact ⟨x,hx,by dsimp only; rw [hxy,e.right_inv hy]⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨e.map_source (hFs x hx),e.symm x,⟨x,hx,rfl⟩,?_⟩
    exact (e.left_inv (hFs x hx)).symm

theorem chart_density_preserved_by_haar_homeomorph [FiniteDimensional ℝ E]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]
    (e : OpenPartialHomeomorph G E) (he1 : 1∈e.source)
    (μ : Measure G) [μ.IsHaarMeasure] [SFinite μ]
    [μ.IsMulRightInvariant] [μ.IsInvInvariant]
    (μE : Measure E) [μE.IsAddHaarMeasure]
    (ρ : E → ℝ)
    (hC : ∀ (g : G) y, y∈e.target → ContDiffAt ℝ 1 (chartLeftMap e g) y)
    (hρ : ∀ (g : G) x, x∈e.target → g*e.symm x∈e.source →
      ρ (chartLeftMap e g x) * |(fderiv ℝ (chartLeftMap e g) x).det| = ρ x)
    (F : G ≃ₜ G) (hF : MeasurePreserving F μ μ)
    {A : Set E} (hA : MeasurableSet A) (hAt : A⊆e.target)
    (hFs : ∀ x∈A, F (e.symm x)∈e.source) :
    (∫⁻ x in (fun y => e (F (e.symm y))) '' A, ENNReal.ofReal (ρ x) ∂μE) =
      ∫⁻ x in A, ENNReal.ofReal (ρ x) ∂μE := by
  let ν := chartDensityMeasure e μE ρ
  let : SFinite ν := by dsimp only [ν,chartDensityMeasure]; infer_instance
  obtain ⟨B,hBnh,hBs,hBk⟩ := local_compact_nhds (e.open_source.mem_nhds he1)
  have hB : MeasurableSet B := hBk.isClosed.measurableSet
  have hB0 : μ B ≠ 0 := (μ.measure_pos_of_mem_nhds hBnh).ne'
  have hBtop : μ B ≠ (∞ : ℝ≥0∞) := hBk.measure_lt_top.ne
  have hIA := chart_inverse_image_measurable e hA hAt
  have hFA : MeasurableSet (F '' (e.symm '' A)) := F.measurableEmbedding.measurableSet_image.mpr hIA
  have hIs : e.symm '' A⊆e.source := by rintro _ ⟨x,hx,rfl⟩; exact e.map_target (hAt hx)
  have hFAs : F '' (e.symm '' A)⊆e.source := by
    rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    exact hFs x hx
  have hmass : μ (F '' (e.symm '' A))=μ (e.symm '' A) :=
    by
      have hh := hF.measure_preimage hFA.nullMeasurableSet
      rw [F.injective.preimage_image] at hh
      exact hh.symm
  have hn := local_haar_equal_mass μ ν e.source
    (chartDensityMeasure_left_overlap e μE ρ hC hρ) hB hBs hB0 hBtop
    hFA hFAs hIA hIs hmass
  dsimp only [ν] at hn
  rw [chartDensityMeasure_apply e μE ρ hFA,chartDensityMeasure_apply e μE ρ hIA,
    chartPart_inverse_image e hAt,chartPart_map_inverse_image e F hAt hFs] at hn
  exact hn
end Release061

end

end OAI
