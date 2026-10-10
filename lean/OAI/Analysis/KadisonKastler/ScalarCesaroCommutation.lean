import OAI.Analysis.KadisonKastler.ScalarShiftLimit
import OAI.Analysis.KadisonKastler.ScalarL2Multiplication

namespace OAI

/-! # Naturality and locality of scalar shift averages -/

namespace KadisonKastler

noncomputable section

open MeasureTheory
open scoped BigOperators

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  (S : X → X) (hS : Measure.QuasiMeasurePreserving S μ μ)

theorem scalarShiftCesaro_commutes (A : ScalarLInfinity μ →L[ℂ] ScalarLInfinity μ)
    (hA : ∀ f, A (scalarInfinityPullback S hS f) = scalarInfinityPullback S hS (A f))
    (n : ℕ) (f : ScalarLInfinity μ) :
    A (scalarShiftCesaro S hS n f) = scalarShiftCesaro S hS n (A f) := by
  have hp (i : ℕ) : A (((scalarInfinityPullbackL S hS) ^ i) f) =
      ((scalarInfinityPullbackL S hS) ^ i) (A f) := by
    induction i with
    | zero => simp
    | succ i hi =>
      rw [pow_succ', mul_apply_eq_comp, mul_apply_eq_comp]
      exact (hA _).trans (congrArg (scalarInfinityPullback S hS) hi)
  simp only [scalarShiftCesaro, smul_apply, sum_apply, map_smul, map_sum, hp]

omit [IsProbabilityMeasure μ] in
theorem scalarInfinityPullback_commutes (T : X → X)
    (hT : Measure.QuasiMeasurePreserving T μ μ)
    (hcomm : ∀ x, S (T x) = T (S x)) (f : ScalarLInfinity μ) :
    scalarInfinityPullback T hT (scalarInfinityPullback S hS f) =
      scalarInfinityPullback S hS (scalarInfinityPullback T hT f) := by
  apply Lp.ext
  filter_upwards [scalarInfinityPullback_ae T hT (scalarInfinityPullback S hS f),
    hT.ae (scalarInfinityPullback_ae S hS f),
    scalarInfinityPullback_ae S hS (scalarInfinityPullback T hT f),
    hS.ae (scalarInfinityPullback_ae T hT f)] with x ha hb hc hd
  rw [ha, hb, hc, hd, hcomm]

def scalarInfinityMulL (b : ScalarLInfinity μ) : ScalarLInfinity μ →L[ℂ] ScalarLInfinity μ :=
  LinearMap.mkContinuous
    { toFun := scalarInfinityMul b
      map_add' f g := by
        rw [scalarInfinityMul_comm b, scalarInfinityMul_add_left,
          scalarInfinityMul_comm f, scalarInfinityMul_comm g]
      map_smul' c f := by
        simp only [RingHom.id_apply]
        rw [scalarInfinityMul_comm b, scalarInfinityMul_smul_left, scalarInfinityMul_comm f] }
    ‖b‖ (norm_scalarInfinityMul_le b)

omit [IsProbabilityMeasure μ] in
@[simp]
theorem scalarInfinityMulL_apply (b f : ScalarLInfinity μ) :
    scalarInfinityMulL b f = scalarInfinityMul b f := rfl

theorem scalarShiftCesaro_module (b : ScalarLInfinity μ)
    (hb : scalarInfinityPullback S hS b = b) (n : ℕ) (f : ScalarLInfinity μ) :
    scalarShiftCesaro S hS n (scalarInfinityMul b f) =
      scalarInfinityMul b (scalarShiftCesaro S hS n f) := by
  apply Eq.symm
  apply scalarShiftCesaro_commutes S hS (scalarInfinityMulL b)
  intro g
  simp only [scalarInfinityMulL_apply, scalarInfinityPullback_mul, hb]

end

end KadisonKastler

end OAI
