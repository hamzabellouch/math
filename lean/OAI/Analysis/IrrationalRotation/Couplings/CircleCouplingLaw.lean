import OAI.Analysis.IrrationalRotation.Model.CircleCoupling
import OAI.Analysis.IrrationalRotation.Couplings.CircleCouplingParameters
import OAI.Analysis.IrrationalRotation.Sampling.CircleDigitCrossings
import OAI.Analysis.IrrationalRotation.Product.IndependentCoordinateConditioning

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling

lemma tag_bounds (j s : ℕ) : 0 ≤ tag j s ∧ tag j s ≤ 1 := by
  unfold tag
  split_ifs <;> norm_num

lemma initialLaw_isProbabilityMeasure : IsProbabilityMeasure initialLaw := by
  have := baseLaw_isProbabilityMeasure
  unfold initialLaw
  infer_instance

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma coordinateLaw_isProbabilityMeasure (j i : ℕ) :
    IsProbabilityMeasure (coordinateLaw p j i) := by
  by_cases hi : i = 0
  · simpa [coordinateLaw, hi] using initialLaw_isProbabilityMeasure
  have hs := p.blockIndex_pos hp.m_pos (show 1 ≤ i by omega)
  have hm : (100 : ℝ) ≤ p.m (p.blockIndex i) := by
    exact_mod_cast (show 100 ≤ p.m (p.blockIndex i) by have := hp.m_ge_200 _ hs; omega)
  simpa only [coordinateLaw, ite_eq_right hi] using rawLaw_isProbabilityMeasure
    (CircleParameterLaws.coupling_kappa_bounds _ hs).1
    (CircleParameterLaws.coupling_kappa_bounds _ hs).2 hm
    (hp.coupling_a_bounds _ hs).1 (hp.coupling_a_bounds _ hs).2
    (hp.coupling_b_bounds _ hs).1 (hp.coupling_b_bounds _ hs).2
    (tag_bounds j _).1 (tag_bounds j _).2

lemma law_isProbabilityMeasure (j : ℕ) : IsProbabilityMeasure (law p j) := by
  let := coordinateLaw_isProbabilityMeasure hp j
  unfold law
  infer_instance

omit hp in
lemma measurable_observedDigit (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (side : Bool) (i : ℕ) : Measurable (observedDigit p hr side i) := by
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  change Measurable (UniformQuantization.quantize _ ∘ endpoint side)
  apply (UniformQuantization.measurable_quantize _).comp
  cases side
  · exact measurable_fst.comp measurable_snd
  · exact measurable_snd.comp measurable_snd

omit hp in
lemma measurable_digits (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) :
    Measurable (digits p hr side) := by
  exact Measurable.of_eval (fun i =>
    (measurable_observedDigit hr side i).comp (measurable_pi_apply i))

omit hp in
lemma measurable_label (i : ℕ) : Measurable (label i) := by
  exact measurable_fst.comp (measurable_pi_apply i)

lemma iCondIndepFun_labels_digits (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) :
    letI := law_isProbabilityMeasure hp j
    iCondIndepFun (MeasurableSpace.comap (digits p hr side) inferInstance)
      (measurable_digits hr side).comap_le label (law p j) := by
  let := coordinateLaw_isProbabilityMeasure hp j
  let := law_isProbabilityMeasure hp j
  exact CoordinateConditioning.iCondIndepFun_labels (coordinateLaw p j)
    (observedDigit p hr side) (measurable_observedDigit hr side)
    (fun _ => Prod.fst) (fun _ => measurable_fst)

lemma posterior_isMarkov (j : ℕ) (side : Bool) (i : ℕ) :
    IsMarkovKernel (posterior p j side i) := by
  by_cases hi : i = 0
  · simp only [posterior, ite_eq_left hi]
    infer_instance
  have hs := p.blockIndex_pos hp.m_pos (show 1 ≤ i by omega)
  have hm : (100 : ℝ) ≤ p.m (p.blockIndex i) := by
    exact_mod_cast (show 100 ≤ p.m (p.blockIndex i) by have := hp.m_ge_200 _ hs; omega)
  let : NeZero (MixedRadix.radices p.q i) :=
    ⟨Nat.ne_of_gt (MixedRadix.radices_pos hp.q_pos hp.frequency_increasing hp.frequency_divisible i)⟩
  simpa only [posterior, ite_eq_right hi] using labelsGivenDigit_isMarkov
    (CircleParameterLaws.coupling_kappa_bounds _ hs).1
    (CircleParameterLaws.coupling_kappa_bounds _ hs).2 hm
    (hp.coupling_a_bounds _ hs).1 (hp.coupling_a_bounds _ hs).2
    (hp.coupling_b_bounds _ hs).1 (hp.coupling_b_bounds _ hs).2
    (tag_bounds j _).1 (tag_bounds j _).2 side (MixedRadix.radices p.q i)

end Invariant233.CircleCoupling

end

end OAI
