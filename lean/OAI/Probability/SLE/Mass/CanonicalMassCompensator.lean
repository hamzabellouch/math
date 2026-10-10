import OAI.Probability.SLE.Geometry.WeightedCompactTerminal

namespace OAI

/-! Predictable dyadic recovery for the actual compact weighted canonical
mass. The time argument is the one used by the given filtration. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

def compensatorMeshFiltration {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ) (n : ℕ) : Filtration ℕ mΩ where
  seq i := ℱ (compensatorMeshTime n i)
  mono' := fun _ _ h => ℱ.mono (compensatorMeshTime_mono n h)
  le' _i := ℱ.le _

namespace Multipoint.CanonicalMass

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

theorem compactWeightedMass_compensator_recovery
    (w : C(upperHalfPlane,ℝ≥0)) (K : Set upperHalfPlane) (hK : IsCompact K)
    (T : Ω → ℝ≥0∞) (hT : Measurable T) :
    TendstoInMeasure P
      (fun n ω => meshMassCompensator P
        (compensatorMeshFiltration (Filtration.natural B (fun r =>
          (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)))
        (fun t ω => compactWeightedMass w K (C.process t ω)) n
        (compensatorStopIndex n (T ω)) ω) atTop
      (fun ω => massAtExtendedTime (fun t => compactWeightedMass w K (C.process t ω))
        (compactWeightedMass w K (C.rational.terminal ω)) (T ω)) := by
  apply meshMassCompensator_stopped_tendstoInMeasure P _ _ _ _ _
    (C.compactWeightedMass_terminal_memLp w K hK) (C.compactWeightedMass_paths w K hK) T hT
  · intro t
    exact (compactWeightedMass_measurable w K hK.measurableSet).comp
      (C.progressive.adapted.measurable (i := t))
  · intro n i
    exact ((compactWeightedMass_measurable w K hK.measurableSet).comp
      (C.progressive.adapted (compensatorMeshTime n i))).stronglyMeasurable

end Multipoint.CanonicalMass
end SLEExactGauge

end

end OAI
