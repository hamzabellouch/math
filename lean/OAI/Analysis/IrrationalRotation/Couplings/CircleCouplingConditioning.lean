import OAI.Analysis.IrrationalRotation.Couplings.CircleCouplingDisintegration
import OAI.Analysis.IrrationalRotation.Couplings.CircleCouplingNonterminal
import OAI.Analysis.IrrationalRotation.Couplings.ConditionalObservationTransport
import OAI.Analysis.IrrationalRotation.Sampling.MixedRadixTransport

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators ProbabilityTheory
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma measurable_point (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) :
    Measurable (point p hr side) :=
  (MixedRadix.measurable_circleValue
    (MixedRadix.radices_ge_two hp.q_pos hp.frequency_increasing hp.frequency_divisible)).comp
    (measurable_digits hr side)

lemma ae_recover_digits (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) :
    ∀ᵐ ω ∂law p j, MixedRadix.circleCanonical (MixedRadix.radices p.q) hr
      (point p hr side ω) = digits p hr side ω := by
  filter_upwards [ae_nonterminal_digits hp j hr side] with ω hω
  exact MixedRadix.circleCanonical_circleValue hr _ hω

lemma iCondIndepFun_labels_point (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) :
    letI := law_isProbabilityMeasure hp j
    iCondIndepFun (MeasurableSpace.comap (point p hr side) inferInstance)
      (measurable_point hp hr side).comap_le label (law p j) := by
  let := law_isProbabilityMeasure hp j
  exact (ConditionalObservationTransport.iCondIndepFun_encoding_iff
    (measurable_digits hr side)
    (MixedRadix.measurable_circleValue
      (MixedRadix.radices_ge_two hp.q_pos hp.frequency_increasing hp.frequency_divisible))
    (MixedRadix.measurable_circleCanonical _ hr) (ae_recover_digits hp j hr side)
    label measurable_label).2 (iCondIndepFun_labels_digits hp j hr side)

lemma condExp_labels_digits (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool)
    (S : Finset ℕ) (C : ℕ → Set Label) (hC : ∀ i, MeasurableSet (C i)) :
    (law p j)⟦(⋂ i ∈ S, label i ⁻¹' C i) |
      MeasurableSpace.comap (digits p hr side) inferInstance⟧ =ᵐ[law p j]
      (fun ω => ∏ i ∈ S, (posterior p j side i (digits p hr side ω i)).real (C i)) := by
  let := coordinateLaw_isProbabilityMeasure hp j
  let := posterior_isMarkov hp j side
  exact CoordinateConditioning.condExp_label_inter_of_disintegration (coordinateLaw p j)
    S (observedDigit p hr side) (measurable_observedDigit hr side)
    (fun _ => Prod.fst) (fun _ => measurable_fst) (posterior p j side)
    (fun i => (posterior_disintegration hp j hr side i).symm) C hC

lemma condExp_labels_point (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool)
    (S : Finset ℕ) (C : ℕ → Set Label) (hC : ∀ i, MeasurableSet (C i)) :
    (law p j)⟦(⋂ i ∈ S, label i ⁻¹' C i) |
      MeasurableSpace.comap (point p hr side) inferInstance⟧ =ᵐ[law p j]
      (fun ω => ∏ i ∈ S, (posterior p j side i
        (MixedRadix.circleCanonical (MixedRadix.radices p.q) hr (point p hr side ω) i)).real (C i)) := by
  let := law_isProbabilityMeasure hp j
  have he := ConditionalObservationTransport.condExp_encoding
    (measurable_digits hr side)
    (MixedRadix.measurable_circleValue
      (MixedRadix.radices_ge_two hp.q_pos hp.frequency_increasing hp.frequency_divisible))
    (MixedRadix.measurable_circleCanonical _ hr) (ae_recover_digits hp j hr side)
    ((⋂ i ∈ S, label i ⁻¹' C i).indicator (fun _ => (1 : ℝ)))
  refine he.trans ((condExp_labels_digits hp j hr side S C hC).trans ?_)
  filter_upwards [ae_recover_digits hp j hr side] with ω hω
  rw [hω]

lemma condExp_single_label_point (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) (i : ℕ) (l : Label) :
    (law p j)⟦label i ⁻¹' {l} | MeasurableSpace.comap (point p hr side) inferInstance⟧ =ᵐ[law p j]
      (fun ω => (posterior p j side i
        (MixedRadix.circleCanonical (MixedRadix.radices p.q) hr (point p hr side ω) i)).real {l}) := by
  simpa using condExp_labels_point hp j hr side {i} (fun _ => {l})
    (fun _ => measurableSet_singleton l)

end Invariant233.CircleCoupling

end

end OAI
