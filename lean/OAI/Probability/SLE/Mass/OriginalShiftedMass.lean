import OAI.Probability.SLE.Mass.CanonicalMassRemaining
import OAI.Probability.SLE.Stochastic.ProgressiveStoppedTime

namespace OAI

/-! The original canonical mass evaluated after a finite stopping time.
Its remaining Green kernel is stated in the full shifted filtration. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint

lemma extendedCanonicalMass_finite_time
    {Ω : Type*} (N : ℝ≥0 → Ω → Measure upperHalfPlane)
    (ν : Ω → Measure upperHalfPlane) (τ : Ω → ℝ≥0) (ω : Ω) :
    extendedCanonicalMass N ν (τ ω:ℝ≥0∞) ω=N (τ ω) ω := by
  simp only [extendedCanonicalMass,ENNReal.coe_lt_top,ite_true,ENNReal.toNNReal_coe]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G) (τ : Ω → ℝ≥0)
  (hτ : IsStoppingTime (Filtration.natural B (fun s =>
    (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable))
    (fun ω => (τ ω:WithTop ℝ≥0)))

include C τ hτ in
lemma CanonicalMass.original_shifted_adapted :
    Adapted (shiftedStoppingFiltration hτ) (fun t ω => C.process (τ ω+t) ω) :=
  _root_.OAI.MeasureTheory.IsProgressive.shifted_adapted C.progressive τ hτ

include C τ hτ in
lemma CanonicalMass.original_shifted_green_kernel
    (t : ℝ≥0) (E : Set Ω) (hE : MeasurableSet[shiftedStoppingFiltration hτ t] E) :
    (P.restrict E).bind C.rational.terminal =
      (P.restrict E).bind (fun ω => C.process (τ ω+t) ω)+
      (P.restrict E).bind (fun ω => halfPlaneGreenMeasure κ B γ G (τ ω+t) ω) := by
  have h := C.kernel (fun ω => ((τ ω+t:ℝ≥0):WithTop ℝ≥0))
    (stopping_time_add_nnreal hτ t) E hE
  change (P.restrict E).bind C.rational.terminal =
    (P.restrict E).bind (fun ω => C.process (τ ω+t) ω)+
      (P.restrict E).bind (fun ω => halfPlaneGreenMeasure κ B γ G (τ ω+t) ω) at h
  exact h

include C τ hτ in
lemma CanonicalMass.original_shifted_mean_le (t : ℝ≥0) (E : Set Ω) :
    (P.restrict E).bind (fun ω => C.process (τ ω+t) ω) ≤ initialGreenMeasure κ := by
  have h := C.atTime_mean_le (fun ω => ((τ ω+t:ℝ≥0):ℝ≥0∞))
    (stopping_time_add_nnreal hτ t).measurable' E
  exact h

end SLEExactGauge.Multipoint

end

end OAI
