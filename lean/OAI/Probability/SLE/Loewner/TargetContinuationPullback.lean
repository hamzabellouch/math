import OAI.Probability.SLE.Angle.TargetBrownianNormalization
import OAI.Probability.SLE.Angle.TargetPotentialIncrement

namespace OAI

/-! The prescribed fresh-driver average pulled back to a regular
Brownian presentation, retaining its full natural past. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

local instance pullbackPathMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance pullbackPathBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

theorem continuationMean_comp_condLExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (b : Ω → Driver) (hb : Measurable b)
    (hB : IsBrownianReal (fun t ω => b ω t) P)
    (W : WienerLaw) (hLaw : HasLaw b W P) (t : ℝ≥0)
    (f : Driver → ℝ≥0∞) (hf : Measurable f) :
    (fun ω => continuationMean W t f (b ω)) =ᵐ[P]
      P⁻[(fun ω => f (b ω)) |
        (Filtration.natural (fun t ω => b ω t)
          (fun t => ((continuous_eval_const t).measurable.comp hb).stronglyMeasurable)) t] := by
  have h := source_driver_continuation_condLExp hB
    (fun t => (continuous_eval_const t).measurable.comp hb)
    (fun ω => (b ω).continuous) t (fun p => f (centerDriver p)) (hf.comp measurable_centerDriver)
  change (fun ω => driverContinuationMean (P.map (fun ω => (b ω).toContinuousMap)) t
      (fun p => f (centerDriver p)) (b ω).toContinuousMap) =ᵐ[P]
    P⁻[(fun ω => f (centerDriver (b ω).toContinuousMap)) |
      (Filtration.natural (fun t ω => b ω t)
        (fun t => ((continuous_eval_const t).measurable.comp hb).stronglyMeasurable)) t] at h
  have he : P.map (fun ω => (b ω).toContinuousMap)=W.map (fun p => p.toContinuousMap) := by
    rw [← hLaw.map_eq,Measure.map_map measurable_driverInclusion hb]
    rfl
  rw [he] at h
  have heq : (fun ω => driverContinuationMean (W.map (fun p => p.toContinuousMap)) t
      (fun p => f (centerDriver p)) (b ω).toContinuousMap) =
      (fun ω => continuationMean W t f (b ω)) :=
    funext (fun ω => continuationMean_eq_pathMean W t f hf (b ω))
  rw [heq] at h
  simpa only [centerDriver_inclusion] using h

theorem continuationMean_comp_finite_condExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (b : Ω → Driver) (hb : Measurable b)
    (hB : IsBrownianReal (fun t ω => b ω t) P)
    (W : WienerLaw) (hLaw : HasLaw b W P) (t : ℝ≥0)
    (f : Driver → ℝ≥0∞) (hf : Measurable f)
    (hfin : (∫⁻ ω, f (b ω) ∂P) ≠ ∞) :
    (∀ᵐ ω ∂P, continuationMean W t f (b ω)<∞) ∧
    (fun ω => (continuationMean W t f (b ω)).toReal) =ᵐ[P]
      P[(fun ω => (f (b ω)).toReal) |
        (Filtration.natural (fun t ω => b ω t)
          (fun t => ((continuous_eval_const t).measurable.comp hb).stronglyMeasurable)) t] := by
  have he := continuationMean_comp_condLExp b hb hB W hLaw t f hf
  let m := (Filtration.natural (fun t ω => b ω t)
    (fun t => ((continuous_eval_const t).measurable.comp hb).stronglyMeasurable)) t
  constructor
  · filter_upwards [he,condLExp_lt_top (mΩ := m) hfin] with ω hω hh
    exact hω.symm ▸ hh
  · exact (he.fun_comp ENNReal.toReal).trans (toReal_condLExp m (hf.comp hb).aemeasurable hfin)

theorem potentialDifference_comp_eq_current_sub_condExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (b : Ω → Driver) (hb : Measurable b)
    (hB : IsBrownianReal (fun t ω => b ω t) P)
    (W : WienerLaw) (hLaw : HasLaw b W P) (κ θ : ℝ) (n i : ℕ)
    (hm : ∀ j, Measurable (fun b => potential κ θ b (compensatorMeshTime n j)))
    (hfin : ∀ j, (∫⁻ ω, potential κ θ (b ω) (compensatorMeshTime n j) ∂P) ≠ ∞) :
    (fun ω => potentialDifference κ θ W (b ω) n i) =ᵐ[P]
      (fun ω => (potential κ θ (b ω) (compensatorMeshTime n i)).toReal -
        condExp ((Filtration.natural (fun t ω => b ω t)
          (fun t => ((continuous_eval_const t).measurable.comp hb).stronglyMeasurable))
            (compensatorMeshTime n i)) P
          (fun ω => (potential κ θ (b ω) (compensatorMeshTime n (i+1))).toReal) ω) := by
  have h := continuationMean_comp_finite_condExp b hb hB W hLaw
    (compensatorMeshTime n i)
    (fun b => potential κ θ b (compensatorMeshTime n (i+1))) (hm (i+1)) (hfin (i+1))
  filter_upwards [ae_lt_top ((hm i).comp hb) (hfin i),h.1,h.2] with ω hv hw he
  have hnext : ((i:ℝ)+1)*mesh n=(compensatorMeshTime n (i+1):ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using mesh_eq_compensatorMeshTime n (i+1)
  simp only [potentialDifference,mesh_eq_compensatorMeshTime,hnext]
  change (if potential κ θ (b ω) (compensatorMeshTime n i)<∞ ∧
      continuationMean W (compensatorMeshTime n i)
        (fun b => potential κ θ b (compensatorMeshTime n (i+1))) (b ω)<∞
      then _ else _)=_
  rw [ite_eq_left ⟨hv,hw⟩]
  dsimp only [continuationMean] at he
  rw [he]

end SLEExactGauge.Target

end

end OAI
