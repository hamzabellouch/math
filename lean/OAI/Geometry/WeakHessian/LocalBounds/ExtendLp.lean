import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.BoundedMulLp

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
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {X : Type*} [MeasurableSpace X] {m ν : Measure X}

def zeroExtendLp {s : Set X} (hs : MeasurableSet s) :
    Lp ℝ 2 (m.restrict s) →L[ℝ] Lp ℝ 2 m :=
  LinearMap.mkContinuous
    { toFun := fun f => ((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).toLp
        (s.indicator (f : X → ℝ))
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [((memLp_indicator_iff_restrict hs).mpr (Lp.memLp (f+g))).coeFn_toLp,
          ((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).coeFn_toLp,
          ((memLp_indicator_iff_restrict hs).mpr (Lp.memLp g)).coeFn_toLp,
          Lp.coeFn_add
            (((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).toLp (s.indicator (f : X → ℝ)))
            (((memLp_indicator_iff_restrict hs).mpr (Lp.memLp g)).toLp (s.indicator (g : X → ℝ))),
          (ae_restrict_iff' hs).mp (Lp.coeFn_add f g)] with x hfg hf hg hadd hlocal
        rw [hfg,hadd,Pi.add_apply,hf,hg]
        by_cases hx : x ∈ s
        · simp only [indicator_of_mem hx,hlocal hx,Pi.add_apply]
        · simp only [indicator_of_notMem hx,add_zero]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [((memLp_indicator_iff_restrict hs).mpr (Lp.memLp (c • f))).coeFn_toLp,
          ((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).coeFn_toLp,
          Lp.coeFn_smul c
            (((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).toLp (s.indicator (f : X → ℝ))),
          (ae_restrict_iff' hs).mp (Lp.coeFn_smul c f)] with x hcf hf hsm hlocal
        simp only [RingHom.id_apply]
        rw [hcf,hsm,Pi.smul_apply,hf]
        by_cases hx : x ∈ s
        · simp only [indicator_of_mem hx,hlocal hx,Pi.smul_apply]
        · simp only [indicator_of_notMem hx,smul_zero] }
    1 (by
      intro f
      change ‖((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).toLp (s.indicator (f : X → ℝ))‖ ≤ 1*‖f‖
      rw [one_mul, Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hs]
      exact le_rfl)

lemma zeroExtendLp_ae {s : Set X} (hs : MeasurableSet s) (f : Lp ℝ 2 (m.restrict s)) :
    zeroExtendLp hs f =ᵐ[m] s.indicator (f : X → ℝ) :=
  ((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).coeFn_toLp

def cutoffChangeLp {s : Set X} (hs : MeasurableSet s) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hlocal : m.restrict s ≤ c • ν) {φ : X → ℝ}
    (hφ : AEStronglyMeasurable φ (m.restrict s)) {B : ℝ}
    (hB : ∀ᵐ x ∂m.restrict s, |φ x| ≤ B) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 m :=
  (zeroExtendLp hs).comp ((boundedMulLp hφ hB).comp (Lp.LpToLpOfMeasureLeSMul hc hlocal))

lemma cutoffChangeLp_ae {s : Set X} (hs : MeasurableSet s) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hlocal : m.restrict s ≤ c • ν) {φ : X → ℝ}
    (hφ : AEStronglyMeasurable φ (m.restrict s)) {B : ℝ}
    (hB : ∀ᵐ x ∂m.restrict s, |φ x| ≤ B)
    (hz : ∀ x ∉ s, φ x = 0) (f : Lp ℝ 2 ν) :
    cutoffChangeLp hs hc hlocal hφ hB f =ᵐ[m] (fun x => f x*φ x) := by
  filter_upwards [zeroExtendLp_ae hs
    (boundedMulLp hφ hB (Lp.LpToLpOfMeasureLeSMul hc hlocal f)),
    (ae_restrict_iff' hs).mp (boundedMulLp_ae hφ hB (Lp.LpToLpOfMeasureLeSMul hc hlocal f)),
    (ae_restrict_iff' hs).mp (Lp.coeFn_LpToLpOfMeasureLeSMul hc hlocal f)] with x hx hy hz'
  change (zeroExtendLp hs (boundedMulLp hφ hB (Lp.LpToLpOfMeasureLeSMul hc hlocal f))) x = _
  rw [hx]
  by_cases hxs : x ∈ s
  · rw [indicator_of_mem hxs,hy hxs,hz' hxs]
  · rw [indicator_of_notMem hxs,hz x hxs,mul_zero]

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end
end InlinedFile0

end OAI
