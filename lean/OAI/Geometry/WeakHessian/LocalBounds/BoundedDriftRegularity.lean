import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.WeightedDriftResolvent
import OAI.Geometry.WeakHessian.HeatFlow.LaplacianResolventUnique

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile154
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.bounded_weighted_laplacian_lipschitz {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    {ξ A : X → ℝ} (hA : IsLaplacian (exponentialMeasure m V) ξ A)
    {Bξ BA : ℝ} (hξ : ∀ᵐ x ∂exponentialMeasure m V,|ξ x| ≤ Bξ)
    (hAb : ∀ᵐ x ∂exponentialMeasure m V,|A x| ≤ BA) :
    ∃ g : X → ℝ,GloballyLipschitz g ∧ g =ᵐ[exponentialMeasure m V] ξ := by
  obtain ⟨τ,hτ,hL2,hLinf⟩ := positive_small_drift_time K L
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hBV
  have hξm : Sobolev m ξ := (sobolev_exponentialMeasure_iff hBV ξ).mpr hA.1
  have hAm : MemLp A 2 m := hA.2.1.of_measure_le_smul ENNReal.ofReal_ne_top hm
  let f : X → ℝ := fun x => τ⁻¹*ξ x-A x
  have hf : MemLp f 2 m := (hξm.1.const_mul τ⁻¹).sub hAm
  let u := hf.toLp f
  let B := τ⁻¹*|Bξ|+|BA|
  have hB : 0 ≤ B := add_nonneg (mul_nonneg (inv_nonneg.mpr hτ.le) (abs_nonneg _)) (abs_nonneg _)
  have hu : ∀ᵐ x ∂m,|u x| ≤ B := by
    filter_upwards [hf.coeFn_toLp,(Measure.absolutelyContinuous_of_le_smul hm).ae_le hξ,
      (Measure.absolutelyContinuous_of_le_smul hm).ae_le hAb] with x he hx ha
    change |hf.toLp f x| ≤ _
    rw [he]
    dsimp [f,B]
    calc
      |τ⁻¹*ξ x-A x| ≤ |τ⁻¹*ξ x|+|A x| := abs_sub _ _
      _ = τ⁻¹*|ξ x|+|A x| := by rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr hτ.le)]
      _ ≤ τ⁻¹*|Bξ|+|BA| := add_le_add
        (mul_le_mul_of_nonneg_left (hx.trans (le_abs_self _)) (inv_nonneg.mpr hτ.le))
        (ha.trans (le_abs_self _))
  obtain ⟨r,g,hg,he,hr⟩ := hrcd.bounded_drift_resolvent hN hfull hfin o hV hBV hτ hL2 hLinf u hB hu
  have hξeq : IsLaplacian (exponentialMeasure m V) ξ (fun x => τ⁻¹*ξ x-u x) := by
    apply hA.congr_ae EventuallyEq.rfl
    filter_upwards [(Measure.absolutelyContinuous_of_le_smul hν).ae_le hf.coeFn_toLp] with x hx
    change A x=τ⁻¹*ξ x-hf.toLp f x
    rw [hx]
    dsimp [f]
    ring
  have hnfin := hfin.of_le_smul (C := (Real.exp BV).toNNReal) hν
  have hnpar := (hrcd.1.global_localGradientParallelogram hfin o hrcd.2).change_measure
    (C := (Real.exp BV).toNNReal) (D := (Real.exp BV).toNNReal) hm hν
  have hre := hr.positive_resolvent_unique hnfin hnpar (inv_pos.mpr hτ) hξeq
  have hgr : g =ᵐ[exponentialMeasure m V] r := (Measure.absolutelyContinuous_of_le_smul hν).ae_le he
  exact ⟨g,hg,hgr.trans hre⟩
end WeakHessian

end
end InlinedFile154

end OAI
