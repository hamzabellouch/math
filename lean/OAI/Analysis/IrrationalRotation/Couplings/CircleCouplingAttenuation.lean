import OAI.Analysis.IrrationalRotation.Model.CircleTailAttenuation
import OAI.Analysis.IrrationalRotation.Couplings.CircleCouplingTagSupport
import OAI.Analysis.IrrationalRotation.Couplings.ConditionalAvoidance
import OAI.Analysis.IrrationalRotation.Analysis.ParameterTailAttenuation

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData CouplingMarginalBounds
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

omit hp in
lemma measurableSet_tagEvent (p : CircleParameterData) (j : ℕ) :
    MeasurableSet (tagEvent p j) := by
  simp only [tagEvent, Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro i
  by_cases hi : i ∈ p.block j
  · simpa only [hi, true_and] using
      (measurableSet_eq_fun (measurable_label i) (measurable_const (a := (some 4 : Label))))
  · simp only [hi, false_and, Set.ofPred_false, MeasurableSet.empty]

lemma actual_tail_attenuation_of_ac_order (j : ℕ) (hj : 1 ≤ j)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (hac : ∀ side, (law p j).map (point p hr side) ≪ circleMeasure)
    (horder : ∀ᵐ ω ∂law p j, ∀ i : p.Coord,
      p.coordinate i.2 (point p hr false ω) ≤ p.coordinate i.2 (point p hr true ω)) :
    TailAttenuation θ p j hr := by
  let := law_isProbabilityMeasure hp j
  have hpoint (side : Bool) : Measurable[endpointSigma p hr side] (point p hr side) :=
    Measurable.of_comap_le le_rfl
  have hle (side : Bool) : endpointSigma p hr side ≤ (inferInstance : MeasurableSpace Sample) :=
    (measurable_point hp hr side).comap_le
  let top : Bool → ℕ → Set Sample := fun which i => label i ⁻¹' {topLabel which}
  let bottom : Bool → ℕ → Set Sample := fun which i => label i ⁻¹' {bottomLabel which}
  have ht (which : Bool) (i : ℕ) : MeasurableSet (top which i) :=
    (measurable_label i) (measurableSet_singleton _)
  have hb (which : Bool) (i : ℕ) : MeasurableSet (bottom which i) :=
    (measurable_label i) (measurableSet_singleton _)
  have hindt (which : Bool) : iCondIndepSet (endpointSigma p hr false) (hle false)
      (top which) (law p j) :=
    ConditionalAvoidance.iCondIndepSet_preimages (hle false) label measurable_label
      (iCondIndepFun_labels_point hp j hr false) (fun _ => {topLabel which})
      (fun _ => measurableSet_singleton _)
  have hindb (which : Bool) : iCondIndepSet (endpointSigma p hr true) (hle true)
      (bottom which) (law p j) :=
    ConditionalAvoidance.iCondIndepSet_preimages (hle true) label measurable_label
      (iCondIndepFun_labels_point hp j hr true) (fun _ => {bottomLabel which})
      (fun _ => measurableSet_singleton _)
  intro k hk
  apply hp.parameter_tail_conditional_attenuation (endpointSigma p hr false)
    (endpointSigma p hr true) (hle false) (hle true) (law p j)
    (point p hr false) (point p hr true) (hpoint false) (hpoint true)
    (hac false) (hac true) horder top bottom ht hb hindt hindb j hj
  · intro s hjs which i hi u hu
    have hs : 1 ≤ s := hj.trans hjs
    filter_upwards [ae_top_forces hp j hr hs hi which,
      ae_bottom_forces hp j hr hs hi which,
      ae_top_conditional_probability hp j hr hs hi which,
      ae_bottom_conditional_probability hp j hr hs hi which]
        with ω htforce hbforce htprob hbprob
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro _hxu hl
      exact htforce u hl hu.2
    · intro _huy hl
      exact hbforce u hl hu.1
    · intro hxu
      exact htprob u hxu hu.2
    · intro huy
      exact hbprob u huy hu.1
  · filter_upwards [ae_all_tag_coordinate_support hp j hr] with ω hω
    rintro ⟨i, hi, htag⟩
    exact ⟨i, hi, hω j hj i hi htag⟩
  · exact hk

end Invariant233.CircleCoupling

end

end OAI
