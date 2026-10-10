import Mathlib
import OAI.Analysis.SymmetricDomains.ChartDensityPreservedBy

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

theorem abs_det_eq_one_of_local_density_preserving
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (S : Set E) (hS : IsOpen S) (f : E → E) (f' : E → E →L[ℝ] E)
    (ρ : E → ℝ)
    (hf : ∀ x∈S, HasFDerivAt f (f' x) x)
    (hinj : InjOn f S)
    (hρ : ContinuousOn ρ S)
    (hρf : ContinuousOn (ρ ∘ f) S)
    (hD : ContinuousOn (fun x => (f' x).det) S)
    (hm : ∀ A : Set E, MeasurableSet A → A⊆S →
      (∫⁻ x in f '' A, ENNReal.ofReal (ρ x) ∂μ) =
        ∫⁻ x in A, ENNReal.ofReal (ρ x) ∂μ)
    {x : E} (hx : x∈S) (hfx : f x=x) (hρx : 0<ρ x) :
    |(f' x).det|=1 := by
  let j : E → ℝ≥0∞ := fun y => ENNReal.ofReal |(f' y).det| * ENNReal.ofReal (ρ (f y))
  let r : E → ℝ≥0∞ := fun y => ENNReal.ofReal (ρ y)
  have hjc : ContinuousOn j S := by
    have hc := ENNReal.continuous_ofReal.comp_continuousOn (hD.abs.mul hρf)
    simpa only [j,Function.comp_def,Pi.mul_apply,ENNReal.ofReal_mul (abs_nonneg _)] using hc
  have hrc : ContinuousOn r S := ENNReal.continuous_ofReal.comp_continuousOn hρ
  have heq : j =ᵐ[μ.restrict S] r := by
    apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀
      (hjc.aemeasurable hS.measurableSet) (hrc.aemeasurable hS.measurableSet)
    intro A hA _
    rw [Measure.restrict_restrict hA]
    have hAS : MeasurableSet (A∩S) := hA.inter hS.measurableSet
    have hd : ∀ y∈A∩S, HasFDerivWithinAt f (f' y) (A∩S) y :=
      fun y hy => (hf y hy.2).hasFDerivWithinAt
    have hh := lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hAS hd
      (hinj.mono inter_subset_right) (fun y => ENNReal.ofReal (ρ y))
    exact hh.symm.trans (hm (A∩S) hAS inter_subset_right)
  have hxj := Measure.eqOn_open_of_ae_eq heq hS hjc hrc hx
  dsimp only [j,r] at hxj
  rw [hfx,← ENNReal.ofReal_mul (abs_nonneg _)] at hxj
  have heqreal : |(f' x).det| * ρ x=ρ x :=
    by
      have ht := congrArg ENNReal.toReal hxj
      simpa only [ENNReal.toReal_ofReal (mul_nonneg (abs_nonneg _) hρx.le),
        ENNReal.toReal_ofReal hρx.le] using ht
  exact (mul_right_cancel₀ hρx.ne' (heqreal.trans (one_mul _).symm))

theorem chart_abs_det_one_of_haar_preserving
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (e : OpenPartialHomeomorph G E) (he1 : 1∈e.source)
    (μ : Measure G) [μ.IsHaarMeasure] [SFinite μ]
    [μ.IsMulRightInvariant] [μ.IsInvInvariant]
    (μE : Measure E) [μE.IsAddHaarMeasure]
    (hC : ∀ (g : G) y, y∈e.target → ContDiffAt ℝ 1 (chartLeftMap e g) y)
    (hD : ∀ (g : G) y, y∈e.target → g*e.symm y∈e.source →
      (fderiv ℝ (chartLeftMap e g) y).det≠0)
    (hρ : ContinuousOn (chartLeftDensity e) e.target)
    (F : G ≃ₜ G) (hF : MeasurePreserving F μ μ) (hF1 : F 1=1)
    (hFC : ∀ y, y∈e.target → ContDiffAt ℝ 1 (fun x => e (F (e.symm x))) y) :
    |(fderiv ℝ (fun x => e (F (e.symm x))) (e 1)).det|=1 := by
  let f : E → E := fun x => e (F (e.symm x))
  let S : Set E := e.target ∩ (fun x => F (e.symm x)) ⁻¹' e.source
  have hSt : S⊆e.target := inter_subset_left
  have hS : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hc : ContinuousAt (fun y => F (e.symm y)) x :=
      F.continuous.continuousAt.comp (e.symm.continuousAt hx.1)
    exact inter_mem (e.open_target.mem_nhds hx.1) (hc (e.open_source.mem_nhds hx.2))
  have hfS : MapsTo f S e.target := fun x hx => e.map_source hx.2
  have hf : ContinuousOn f S := fun x hx => (hFC x hx.1).continuousAt.continuousWithinAt
  have hdet : ContinuousOn (fun x => (fderiv ℝ f x).det) S := by
    intro x hx
    exact (ContinuousLinearMap.continuous_det.continuousAt.comp
      ((hFC x hx.1).continuousAt_fderiv one_ne_zero)).continuousWithinAt
  have hinj : InjOn f S := by
    intro x hx y hy hxy
    exact e.symm.injOn hx.1 hy.1 (F.injective (e.injOn hx.2 hy.2 hxy))
  have hmass (A : Set E) (hA : MeasurableSet A) (hAS : A⊆S) :
      (∫⁻ x in f '' A, ENNReal.ofReal (chartLeftDensity e x) ∂μE) =
        ∫⁻ x in A, ENNReal.ofReal (chartLeftDensity e x) ∂μE :=
    chart_density_preserved_by_haar_homeomorph e he1 μ μE (chartLeftDensity e) hC
      (chartLeftDensity_jacobian e he1 hC hD) F hF hA (hAS.trans hSt)
      (fun x hx => (hAS hx).2)
  have hone : e 1∈S := by
    refine ⟨e.map_source he1,?_⟩
    simpa only [mem_preimage,e.left_inv he1,hF1] using he1
  have hfix : f (e 1)=e 1 := by simp only [f,e.left_inv he1,hF1]
  have hpos : 0<chartLeftDensity e (e 1) := by
    apply inv_pos.mpr
    apply abs_pos.mpr
    apply hD _ _ (e.map_source he1)
    simpa only [e.left_inv he1,one_mul] using he1
  exact abs_det_eq_one_of_local_density_preserving μE S hS f (fderiv ℝ f)
    (chartLeftDensity e) (fun x hx => ((hFC x hx.1).differentiableAt (by simp)).hasFDerivAt)
    hinj (hρ.mono hSt) (hρ.comp hf hfS) hdet hmass hone hfix hpos
end Release061

end

end OAI
