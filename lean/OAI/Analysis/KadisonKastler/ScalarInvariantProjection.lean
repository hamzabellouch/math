import OAI.Analysis.KadisonKastler.ScalarPositiveLimit
import OAI.Analysis.KadisonKastler.ScalarCesaroCommutation

namespace OAI

/-! # A natural positive projection onto shift-invariant scalar functions

The concrete Cesaro construction supplies the limit, its positivity and
contractivity. Weak closure of pullback and bounded multiplication then
proves naturality and the module identity needed by the boundary mean.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  (S : X → X) (hS : Measure.QuasiMeasurePreserving S μ μ)

structure ScalarInvariantProjection where
  toCLM : ScalarLInfinity μ →L[ℂ] ScalarLInfinity μ
  norm_le : ∀ f, ‖toCLM f‖ ≤ ‖f‖
  positive : ∀ f, ScalarNonnegative f → ScalarNonnegative (toCLM f)
  invariant : ∀ f, scalarInfinityPullback S hS (toCLM f) = toCLM f
  fixed : ∀ f, scalarInfinityPullback S hS f = f → toCLM f = f
  weak_limit : ∀ f y, Tendsto
    (fun n => inner ℂ y (scalarInfinityToL2 (scalarShiftCesaro S hS n f)))
    (Ultrafilter.of (atTop : Filter ℕ) : Filter ℕ)
    (𝓝 (inner ℂ y (scalarInfinityToL2 (toCLM f))))

theorem exists_scalarInvariantProjection : Nonempty (ScalarInvariantProjection S hS) := by
  obtain ⟨B, hB, hi, ht⟩ := exists_scalar_shift_limit S hS
    (ContinuousLinearMap.id ℂ (ScalarLInfinity μ)) (fun _ => le_rfl)
  refine ⟨⟨B, hB, ?_, hi, ?_, ht⟩⟩
  · intro f hf
    exact scalarNonnegative_of_weak_limit (fun n => scalarShiftCesaro S hS n f) (B f)
      (scalarNonnegative_shiftCesaro S hS hf) (ht f)
  · intro f hf
    apply scalarInfinityToL2_injective
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (ht f y)
    simpa only [ContinuousLinearMap.id_apply, scalarShiftCesaro_fixed S hS _ f hf] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => inner ℂ y (scalarInfinityToL2 f))
        (Ultrafilter.of (atTop : Filter ℕ) : Filter ℕ) (𝓝 _))

def scalarInvariantProjection : ScalarInvariantProjection S hS :=
  Classical.choice (exists_scalarInvariantProjection S hS)

namespace ScalarInvariantProjection

variable {S hS} (P : ScalarInvariantProjection S hS)

theorem map_const (z : ℂ) : P.toCLM (scalarInfinityConst μ z) = scalarInfinityConst μ z :=
  P.fixed _ (scalarInfinityPullback_const S hS z)

theorem natural (T : X → X) (hT : Measure.QuasiMeasurePreserving T μ μ)
    (hcomm : ∀ x, S (T x) = T (S x)) (f : ScalarLInfinity μ) :
    P.toCLM (scalarInfinityPullback T hT f) = scalarInfinityPullback T hT (P.toCLM f) := by
  apply Eq.symm
  apply scalarInfinityPullback_of_weak_limits
    (l := (Ultrafilter.of (atTop : Filter ℕ) : Filter ℕ)) T hT
    (fun n => scalarShiftCesaro S hS n f)
    (fun n => scalarShiftCesaro S hS n (scalarInfinityPullback T hT f))
    (P.toCLM f) (P.toCLM (scalarInfinityPullback T hT f))
  · intro n
    exact scalarShiftCesaro_commutes S hS (scalarInfinityPullbackL T hT)
      (scalarInfinityPullback_commutes S hS T hT hcomm) n f
  · exact P.weak_limit f
  · exact P.weak_limit _

theorem module_map (b f : ScalarLInfinity μ) (hb : scalarInfinityPullback S hS b = b) :
    P.toCLM (scalarInfinityMul b f) = scalarInfinityMul b (P.toCLM f) := by
  apply Eq.symm
  apply scalarInfinityMul_of_weak_limits
    (l := (Ultrafilter.of (atTop : Filter ℕ) : Filter ℕ)) b
    (fun n => scalarShiftCesaro S hS n f)
    (fun n => scalarShiftCesaro S hS n (scalarInfinityMul b f))
    (P.toCLM f) (P.toCLM (scalarInfinityMul b f))
  · intro n
    exact (scalarShiftCesaro_module S hS b hb n f).symm
  · exact P.weak_limit f
  · exact P.weak_limit _

end ScalarInvariantProjection

end

end KadisonKastler

end OAI
