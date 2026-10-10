import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeat
import OAI.Geometry.WeakHessian.Measure.RadialCutoffLp

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma integrable_fatou_nonneg {f : X → ℝ} (hf : AEStronglyMeasurable f m)
    (hpos : ∀ᵐ x ∂m, 0 ≤ f x) {fs : ℕ → X → ℝ}
    (hfs : ∀ n, Integrable (fs n) m) (hfs0 : ∀ n, ∀ᵐ x ∂m, 0 ≤ fs n x)
    (hlim : ∀ᵐ x ∂m, Tendsto (fun n => fs n x) atTop (𝓝 (f x)))
    {B : ℝ} (hB : ∀ n, (∫ x, fs n x ∂m) ≤ B) :
    Integrable f m ∧ (∫ x,f x ∂m) ≤ B := by
  have H : (∫⁻ x, ENNReal.ofReal (f x) ∂m) ≤ ENNReal.ofReal B := by
    calc
      _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (fs n x)) atTop ∂m := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with x hx
        exact ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (fs n x) ∂m) atTop :=
        lintegral_liminf_le' (fun n => ENNReal.continuous_ofReal.measurable.comp_aemeasurable (hfs n).1.aemeasurable)
      _ ≤ ENNReal.ofReal B := by
        apply liminf_le_of_frequently_le'
        apply Frequently.of_forall
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hfs n) (hfs0 n)]
        exact ENNReal.ofReal_le_ofReal (hB n)
  have hi : Integrable f m := by
    refine ⟨hf, ?_⟩
    change (∫⁻ x, ‖f x‖ₑ ∂m) < ∞
    have he : (fun x => ‖f x‖ₑ) =ᵐ[m] (fun x => ENNReal.ofReal (f x)) :=
      hpos.mono fun x hx => Real.enorm_eq_ofReal hx
    rw [lintegral_congr_ae he]
    exact H.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hi,?_⟩
  have hB0 : 0 ≤ B := (integral_nonneg_of_ae (hfs0 0)).trans (hB 0)
  rw [integral_eq_lintegral_of_nonneg_ae hpos hf]
  simpa only [ENNReal.toReal_ofReal hB0] using ENNReal.toReal_mono ENNReal.ofReal_ne_top H

variable [MetricSpace X] [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

lemma cheegerHeat_submass (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    (hpos : ∀ᵐ x ∂m, 0 ≤ u x) (hi : Integrable u m) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (cheegerHeat h t u) m ∧ (∫ x,cheegerHeat h t u x ∂m) ≤ ∫ x,u x ∂m := by
  let v := cheegerHeat h t u
  have hv : ∀ᵐ x ∂m, 0 ≤ v x := cheegerHeat_nonneg h ht u hpos
  have hchi (n : ℕ) : ∀ᵐ x ∂m, radialCutoffLp hfinite o n x ∈ Icc (0:ℝ) 1 := by
    filter_upwards [radialCutoffLp_ae hfinite o n] with x hx
    rw [hx]
    exact ⟨radialCutoff_nonneg o n x,radialCutoff_le_one o n x⟩
  have hheat (n : ℕ) := cheegerHeat_interval h ht (le_refl (0:ℝ)) zero_le_one _ (hchi n)
  have hsym (n : ℕ) : (∫ x,v x*radialCutoff o n x ∂m) =
      ∫ x,u x*cheegerHeat h t (radialCutoffLp hfinite o n) x ∂m := by
    rw [integral_radialCutoff_eq_inner hfinite o n]
    change ⟪radialCutoffLp hfinite o n,cheegerHeat h t u⟫_ℝ = _
    have H := cheegerHeat_symmetric h t (radialCutoffLp hfinite o n) u
    change ⟪cheegerHeat h t (radialCutoffLp hfinite o n),u⟫_ℝ = ⟪radialCutoffLp hfinite o n,cheegerHeat h t u⟫_ℝ at H
    rw [← H, L2.inner_def]
    rfl
  have hbounded (n : ℕ) : (∫ x,v x*radialCutoff o n x ∂m) ≤ ∫ x,u x ∂m := by
    rw [hsym n]
    apply integral_mono_ae
    · exact hi.mul_bdd (Lp.memLp _).aestronglyMeasurable (by
        filter_upwards [hheat n] with x hx
        change |cheegerHeat h t (radialCutoffLp hfinite o n) x| ≤ (1:ℝ)
        rw [abs_of_nonneg hx.1]; exact hx.2)
    · exact hi
    · filter_upwards [hpos,hheat n] with x hx hc
      exact mul_le_of_le_one_right hx hc.2
  apply integrable_fatou_nonneg (Lp.memLp v).aestronglyMeasurable hv
    (fs := fun n x => v x*radialCutoff o n x)
  · intro n
    exact (Lp.memLp v).integrable_mul (sobolev_of_lipschitz_compactSupport hfinite (radialCutoff_lipschitz o n) (radialCutoff_compact o n)).1
  · intro n
    exact hv.mono fun x hx => mul_nonneg hx (radialCutoff_nonneg o n x)
  · exact ae_of_all _ fun x => by
      simpa only [mul_one] using (tendsto_const_nhds (x := v x)).mul (radialCutoff_tendsto o x)
  · exact hbounded
end WeakHessian

end
end InlinedFile0

end OAI
