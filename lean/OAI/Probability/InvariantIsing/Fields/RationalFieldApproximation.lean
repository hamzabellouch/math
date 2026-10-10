import OAI.Probability.InvariantIsing.Fields.FieldCouplingExtension
import OAI.Probability.InvariantIsing.Magnetic.MagneticFiniteLawExtension
import OAI.Probability.InvariantIsing.Fields.RationalFieldLaw

namespace OAI

/-! Every convergent finite rational approximation gives the same magnetic value. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace InvariantIsing

theorem magneticFieldFunctional_rational_approximation
    (ν μ : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hμ : Integrable (fun x : ℝ => x) (μ : Measure ℝ)) (p : ℕ → RationalFieldLaw)
    (hw : Tendsto (fun n => fieldWassersteinOne (p n).law μ) atTop (𝓝 0)) :
    Tendsto (fun n => (p n).magneticValue (measureR (ν : Measure ℝ) b))
      atTop (𝓝 (magneticFieldFunctional (ν : Measure ℝ) b μ)) := by
  have hh := magneticFieldFunctional_tendsto_wasserstein ν μ (fun n => (p n).law) a b
    hcompact hbound ha hb hμ (fun n => (p n).integrable_id) hw
  have he n := magneticFieldFunctional_finite ν a b hcompact hbound ha hb
    (p n).mass (p n).field (p n).mass_pos (p n).mass_sum (p n).law rfl
  simpa only [he,RationalFieldLaw.magneticValue] using hh

end InvariantIsing

end

end OAI
