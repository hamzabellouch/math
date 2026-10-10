import Mathlib
import OAI.Analysis.SymmetricDomains.ChartLeftDensityJacobian

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

def chartInverseExtension (e : OpenPartialHomeomorph G E) : E → G :=
  by classical exact e.target.piecewise e.symm (fun _ => 1)

omit [IsTopologicalGroup G] [NormedSpace ℝ E] in
theorem chartInverseExtension_measurable (e : OpenPartialHomeomorph G E) :
    Measurable (chartInverseExtension e) := by
  classical
  exact e.continuousOn_invFun.measurable_piecewise continuous_const.continuousOn
    e.open_target.measurableSet

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem chartInverseExtension_eq (e : OpenPartialHomeomorph G E) {x : E}
    (hx : x∈e.target) : chartInverseExtension e x=e.symm x := by
  classical
  simp only [chartInverseExtension,piecewise_eq_of_mem _ _ _ hx]

def chartPart (e : OpenPartialHomeomorph G E) (A : Set G) : Set E :=
  e.target ∩ chartInverseExtension e ⁻¹' A

omit [IsTopologicalGroup G] [NormedSpace ℝ E] in
theorem chartPart_measurable (e : OpenPartialHomeomorph G E) {A : Set G}
    (hA : MeasurableSet A) : MeasurableSet (chartPart e A) :=
  e.open_target.measurableSet.inter (hA.preimage (chartInverseExtension_measurable e))

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem mem_chartPart_iff (e : OpenPartialHomeomorph G E) (A : Set G) (x : E) :
    x∈chartPart e A ↔ x∈e.target ∧ e.symm x∈A := by
  constructor
  · rintro ⟨hx,ha⟩
    exact ⟨hx,by simpa only [mem_preimage,chartInverseExtension_eq e hx] using ha⟩
  · rintro ⟨hx,ha⟩
    exact ⟨hx,by simpa only [mem_preimage,chartInverseExtension_eq e hx] using ha⟩

def chartDensityMeasure (e : OpenPartialHomeomorph G E) (μE : Measure E)
    (ρ : E → ℝ) : Measure G :=
  Measure.map (chartInverseExtension e)
    ((μE.withDensity (fun x => ENNReal.ofReal (ρ x))).restrict e.target)

omit [IsTopologicalGroup G] [NormedSpace ℝ E] in
theorem chartDensityMeasure_apply (e : OpenPartialHomeomorph G E) (μE : Measure E)
    (ρ : E → ℝ) {A : Set G} (hA : MeasurableSet A) :
    chartDensityMeasure e μE ρ A = ∫⁻ x in chartPart e A, ENNReal.ofReal (ρ x) ∂μE := by
  rw [chartDensityMeasure,Measure.map_apply (chartInverseExtension_measurable e) hA,
    Measure.restrict_apply (hA.preimage (chartInverseExtension_measurable e))]
  rw [withDensity_apply _ ((hA.preimage (chartInverseExtension_measurable e)).inter
    e.open_target.measurableSet)]
  apply congrArg (fun S => ∫⁻ x in S, ENNReal.ofReal (ρ x) ∂μE)
  exact Set.inter_comm _ _

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in

theorem chartLeftMap_image_overlap (e : OpenPartialHomeomorph G E)
    (g : G) {A B : Set G} (hAS : A⊆e.source) (hBS : B⊆e.source) :
    chartLeftMap e g '' chartPart e (A ∩ (fun x => g*x) ⁻¹' B) =
      chartPart e (B ∩ (fun y => g⁻¹*y) ⁻¹' A) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    rw [mem_chartPart_iff] at hx ⊢
    have hg : g*e.symm x∈e.source := hBS hx.2.2
    refine ⟨e.map_source hg,?_⟩
    simp only [chartLeftMap,e.left_inv hg,mem_inter_iff,mem_preimage,inv_mul_cancel_left]
    exact ⟨hx.2.2,hx.2.1⟩
  · intro hy
    rw [mem_chartPart_iff] at hy
    have ha : g⁻¹*e.symm y∈e.source := hAS hy.2.2
    refine ⟨e (g⁻¹*e.symm y),?_,?_⟩
    · rw [mem_chartPart_iff]
      refine ⟨e.map_source ha,?_⟩
      simp only [e.left_inv ha,mem_inter_iff,mem_preimage,mul_inv_cancel_left]
      exact ⟨hy.2.2,hy.2.1⟩
    · simp only [chartLeftMap,e.left_inv ha,mul_inv_cancel_left,e.right_inv hy.1]

theorem chartDensityMeasure_left_overlap [FiniteDimensional ℝ E]
    (e : OpenPartialHomeomorph G E) (μE : Measure E) [μE.IsAddHaarMeasure]
    (ρ : E → ℝ)
    (hC : ∀ (g : G) y, y∈e.target → ContDiffAt ℝ 1 (chartLeftMap e g) y)
    (hρ : ∀ (g : G) x, x∈e.target → g*e.symm x∈e.source →
      ρ (chartLeftMap e g x) * |(fderiv ℝ (chartLeftMap e g) x).det| = ρ x)
    (g : G) (A B : Set G) (hA : MeasurableSet A) (hAS : A⊆e.source)
    (hB : MeasurableSet B) (hBS : B⊆e.source) :
    chartDensityMeasure e μE ρ (B ∩ (fun y => g⁻¹*y) ⁻¹' A) =
      chartDensityMeasure e μE ρ (A ∩ (fun x => g*x) ⁻¹' B) := by
  let S := chartPart e (A ∩ (fun x => g*x) ⁻¹' B)
  have hS : MeasurableSet S := chartPart_measurable e
    (hA.inter (hB.preimage (continuous_const.mul continuous_id).measurable))
  have hder : ∀ x∈S, HasFDerivWithinAt (chartLeftMap e g)
      (fderiv ℝ (chartLeftMap e g) x) S x := by
    intro x hx
    exact ((hC g x ((mem_chartPart_iff e _ x).mp hx).1).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hinj : InjOn (chartLeftMap e g) S := by
    intro x hx y hy hxy
    have hx := (mem_chartPart_iff e _ x).mp hx
    have hy := (mem_chartPart_iff e _ y).mp hy
    have heq : g*e.symm x=g*e.symm y := e.injOn (hBS hx.2.2) (hBS hy.2.2) hxy
    exact e.symm.injOn hx.1 hy.1 (mul_left_cancel heq)
  have hmA : MeasurableSet (A ∩ (fun x => g*x) ⁻¹' B) :=
    hA.inter (hB.preimage (continuous_const.mul continuous_id).measurable)
  have hmB : MeasurableSet (B ∩ (fun y => g⁻¹*y) ⁻¹' A) :=
    hB.inter (hA.preimage (continuous_const.mul continuous_id).measurable)
  rw [chartDensityMeasure_apply e μE ρ hmB, chartDensityMeasure_apply e μE ρ hmA,
    ← chartLeftMap_image_overlap e g hAS hBS]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul μE hS hder hinj]
  apply setLIntegral_congr_fun hS
  intro x hx
  have hx := (mem_chartPart_iff e _ x).mp hx
  dsimp only
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  rw [mul_comm,hρ g x hx.1 (hBS hx.2.2)]
end Release061

end

end OAI
