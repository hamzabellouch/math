import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.UpperGradientTendstoNorm
import OAI.Geometry.WeakHessian.LocalBounds.LocalizedSlopeGraphMap

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open WeakHessianFunctional MeasureTheory Set Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m ν : Measure X} [IsProbabilityMeasure ν]

lemma CurvatureDimension.cutoff_cheegerEnergy_le {K N : ℝ}
    (hcd : CurvatureDimension m K N) {C : ℝ≥0} (hν : ν ≤ (C:ℝ≥0∞) • m) (hm : m ≪ ν)
    {f W : Lp ℝ 2 m} (hf : IsLocalWeakUpperGradient m (f : X → ℝ) (W : X → ℝ))
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hcφ : HasCompactSupport φ)
    (hφ0 : ∀ x,0 ≤ φ x) (hφ1 : ∀ x,φ x ≤ 1) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hlocal : m.restrict (tsupport φ) ≤ c • ν) :
    cheegerEnergy m (boundedMulLp hφ.continuous.aestronglyMeasurable
      (ae_of_all m (fun x => by rw [abs_of_nonneg (hφ0 x)]; exact hφ1 x)) f : X → ℝ) ≤
      ENNReal.ofReal ((‖W‖+(L:ℝ)*‖f‖)^2/2) := by
  let J := Lp.LpToLpOfMeasureLeSMul (E := ℝ) (p := 2) ENNReal.coe_ne_top hν
  have hJ (u : Lp ℝ 2 m) : J u =ᵐ[ν] (u : X → ℝ) :=
    Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.coe_ne_top hν u
  have hweak : IsLocalWeakUpperGradient ν (J f : X → ℝ) (J W : X → ℝ) :=
    (hf.of_measure_le_smul hν).congr_ae (hJ f).symm (hJ W).symm
  obtain ⟨D,hD,hDW⟩ := hcd.reference_exists_relaxedGradient_le
    (Measure.absolutelyContinuous_of_le_smul hν) hweak
  have hφB : ∀ x,|φ x| ≤ 1 := fun x => by rw [abs_of_nonneg (hφ0 x)]; exact hφ1 x
  let T := cutoffChangeLp (isClosed_tsupport φ).measurableSet hc hlocal
    hφ.continuous.aestronglyMeasurable (ae_of_all _ hφB)
  let S := cutoffChangeLp (isClosed_tsupport φ).measurableSet hc hlocal
    (measurable_localSlope hφ.continuous).ennreal_toReal.aestronglyMeasurable
    (ae_of_all _ (localSlope_toReal_bound hφ))
  have hT (u : Lp ℝ 2 ν) : T u =ᵐ[m] (fun x => u x*φ x) :=
    cutoffChangeLp_ae _ hc hlocal _ _ (fun _ hx => image_eq_zero_of_notMem_tsupport hx) u
  have hS (u : Lp ℝ 2 ν) : S u =ᵐ[m] (fun x => u x*(localSlope φ x).toReal) :=
    cutoffChangeLp_ae _ hc hlocal _ _ (fun _ hx => by
      rw [localSlope_zero_of_notMem_tsupport hx,ENNReal.toReal_zero]) u
  have hTD : ‖T D‖ ≤ ‖W‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hT D,hm.ae_le hDW,hm.ae_le (hJ W)] with x hx hD hW
    rw [hx,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hD.1 (hφ0 x))]
    calc D x*φ x ≤ D x*1 := mul_le_mul_of_nonneg_left (hφ1 x) hD.1
         _ = D x := mul_one _
         _ ≤ W x := hW ▸ hD.2
         _ ≤ ‖W x‖ := le_abs_self _
  have hSf : ‖S (realAbs_lipschitz.compLp abs_zero (J f))‖ ≤ (L:ℝ)*‖f‖ := by
    calc
      _ ≤ ‖(L:ℝ) • f‖ := by
        apply Lp.norm_le_norm_of_ae_le
        filter_upwards [hS (realAbs_lipschitz.compLp abs_zero (J f)),
          hm.ae_le (realAbs_lipschitz.coeFn_compLp abs_zero (J f)),
          hm.ae_le (hJ f),Lp.coeFn_smul (L:ℝ) f] with x hx hab hfx hsm
        rw [hx,hab,Function.comp_apply,hfx,hsm]
        simp only [Pi.smul_apply,smul_eq_mul,Real.norm_eq_abs,abs_mul,abs_abs,
          abs_of_nonneg (ENNReal.toReal_nonneg),abs_of_nonneg L.coe_nonneg]
        calc |f x| *(localSlope φ x).toReal ≤ |f x| *(L:ℝ) :=
               mul_le_mul_of_nonneg_left ((le_abs_self _).trans (localSlope_toReal_bound hφ x)) (abs_nonneg _)
             _ = (L:ℝ)*|f x| := mul_comm _ _
      _ = (L:ℝ)*‖f‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg L.coe_nonneg]
  have hnorm : ‖T D+S (realAbs_lipschitz.compLp abs_zero (J f))‖ ≤ ‖W‖+(L:ℝ)*‖f‖ :=
    (norm_add_le _ _).trans (add_le_add hTD hSf)
  have hgraph := relaxedGraph_localized hφ hcφ hφ0 hφB hc hlocal hD
  have he : T (J f) = boundedMulLp hφ.continuous.aestronglyMeasurable (ae_of_all m hφB) f := by
    apply Lp.ext
    filter_upwards [hT (J f),hm.ae_le (hJ f),
      boundedMulLp_ae hφ.continuous.aestronglyMeasurable (ae_of_all m hφB) f] with x hx hy hz
    rw [hx,hy,hz]
  have HE := relaxedGraph_energy_le hgraph
  change cheegerEnergy m (T (J f) : X → ℝ) ≤
    ENNReal.ofReal (‖T D+S (realAbs_lipschitz.compLp abs_zero (J f))‖^2/2) at HE
  rw [he] at HE
  exact HE.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
    ((sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm) (by norm_num)))
end WeakHessian

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

end
end InlinedFile0

end OAI
