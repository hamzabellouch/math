import OAI.Analysis.IrrationalRotation.Model.CircleDigitMarginals
import OAI.Analysis.IrrationalRotation.Sampling.CircleDigitEnergy
import OAI.Analysis.IrrationalRotation.Couplings.CircleCouplingLaw
import OAI.Analysis.IrrationalRotation.Sampling.MixedRadixHaarLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling

lemma digitReference_isProbabilityMeasure (p : CircleParameterData)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (i : ℕ) :
    IsProbabilityMeasure (digitReference p hr i) := by
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  unfold digitReference
  infer_instance

lemma rawDensity_memLp (p : CircleParameterData) (j : ℕ) (side : Bool) (i : ℕ) :
    MemLp (rawDensity p j side i) 2 baseLaw := by
  unfold rawDensity
  split_ifs
  · exact memLp_const 1
  · exact marginalDensity_memLp _ _ _ _ _ _

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma rawDensity_laws (j : ℕ) (side : Bool) (i : ℕ) :
    (∀ x, 0 ≤ rawDensity p j side i x ∧ rawDensity p j side i x ≤ 10) ∧
      (∫ x, rawDensity p j side i x ∂baseLaw) = 1 ∧
      (∫ x, (rawDensity p j side i x - 1) ^ 2 ∂baseLaw) ≤
        (if i = 0 then 0 else 50 *
          (kappa (p.blockIndex i) ^ 2 / (p.m (p.blockIndex i) : ℝ) +
            tag j (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ))) := by
  by_cases hi : i = 0
  · simp [rawDensity, hi]
  have hs := p.blockIndex_pos hp.m_pos (show 1 ≤ i by omega)
  have hm : (100 : ℝ) ≤ p.m (p.blockIndex i) := by
    exact_mod_cast (show 100 ≤ p.m (p.blockIndex i) by have := hp.m_ge_200 _ hs; omega)
  have hκ := CircleParameterLaws.coupling_kappa_bounds _ hs
  have ha := hp.coupling_a_bounds _ hs
  have hb := hp.coupling_b_bounds _ hs
  have ht := tag_bounds j (p.blockIndex i)
  simp only [rawDensity, ite_eq_right hi]
  refine ⟨fun x => ?_, marginalDensity_integral hm ha.1 ha.2 hb.1 hb.2 side,
    marginalDensity_energy hm ha.1 ha.2 hb.1 hb.2 ht.1 ht.2 side⟩
  have hx := marginalDensity_bounds hκ.1 hκ.2 hm ha.1 ha.2 hb.1 hb.2 ht.1 ht.2 side x
  exact ⟨(by norm_num : (0 : ℝ) ≤ 49 / 50).trans hx.1, hx.2.2.le⟩

lemma coordinateLaw_map_endpoint (j : ℕ) (side : Bool) (i : ℕ) :
    (coordinateLaw p j i).map (endpoint side) =
      baseLaw.withDensity (fun x => ENNReal.ofReal (rawDensity p j side i x)) := by
  by_cases hi : i = 0
  · simp only [coordinateLaw, rawDensity, ite_eq_left hi]
    unfold initialLaw
    rw [Measure.map_map (by cases side; exact measurable_fst.comp measurable_snd; exact measurable_snd.comp measurable_snd)
      (show Measurable (fun x : ℝ => ((none : Label), (x, x))) from by fun_prop)]
    cases side <;> simp [endpoint, Function.comp_def]
  have hs := p.blockIndex_pos hp.m_pos (show 1 ≤ i by omega)
  have hm : (100 : ℝ) ≤ p.m (p.blockIndex i) := by
    exact_mod_cast (show 100 ≤ p.m (p.blockIndex i) by have := hp.m_ge_200 _ hs; omega)
  have hκ := CircleParameterLaws.coupling_kappa_bounds _ hs
  have ha := hp.coupling_a_bounds _ hs
  have hb := hp.coupling_b_bounds _ hs
  have ht := tag_bounds j (p.blockIndex i)
  simpa only [coordinateLaw, rawDensity, ite_eq_right hi] using
    rawLaw_map_endpoint hκ.1 hκ.2 hm ha.1 ha.2 hb.1 hb.2 ht.1 ht.2 side

lemma observedDigit_density (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) (i : ℕ) :
    (coordinateLaw p j i).map (observedDigit p hr side i) =
      (digitReference p hr i).withDensity
        (fun d => ENNReal.ofReal (digitDensity p hr j side i d)) := by
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  change (coordinateLaw p j i).map (UniformQuantization.quantize _ ∘ endpoint side) = _
  rw [← Measure.map_map (UniformQuantization.measurable_quantize _)
    (by cases side; exact measurable_fst.comp measurable_snd; exact measurable_snd.comp measurable_snd), coordinateLaw_map_endpoint hp]
  have hh := (rawDensity_memLp p j side i).integrable (by norm_num)
  have hn : ∀ᵐ x ∂baseLaw, 0 ≤ rawDensity p j side i x :=
    Filter.Eventually.of_forall (fun x => ((rawDensity_laws hp j side i).1 x).1)
  rw [baseLaw_eq_restrict] at hh hn ⊢
  exact UniformQuantization.map_withDensity_quantize _ hh hn

lemma digitDensity_laws (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) (i : ℕ) :
    (∀ d, 0 ≤ digitDensity p hr j side i d ∧ digitDensity p hr j side i d ≤ 10) ∧
      (∫ d, digitDensity p hr j side i d ∂digitReference p hr i) = 1 ∧
      (∫ d, (digitDensity p hr j side i d - 1) ^ 2 ∂digitReference p hr i) ≤
        (if i = 0 then 0 else 50 *
          (kappa (p.blockIndex i) ^ 2 / (p.m (p.blockIndex i) : ℝ) +
            tag j (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ))) := by
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  have hraw := rawDensity_laws hp j side i
  have hh := rawDensity_memLp p j side i
  rw [baseLaw_eq_restrict] at hh hraw
  refine ⟨fun d => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact UniformQuantization.binAverage_nonneg _
      (Filter.Eventually.of_forall (fun x => (hraw.1 x).1)) d
  · exact UniformQuantization.binAverage_le _ (hh.integrable (by norm_num))
      (Filter.Eventually.of_forall (fun x => (hraw.1 x).2)) d
  · exact (UniformQuantization.integral_binAverage _ (hh.integrable (by norm_num))).trans hraw.2.1
  · exact (UniformQuantization.integral_binAverage_energy_le _ hh).trans hraw.2.2

lemma digitDensity_memLp (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) (i : ℕ) :
    MemLp (digitDensity p hr j side i) 2 (digitReference p hr i) := by
  have := digitReference_isProbabilityMeasure p hr i
  exact memLp_of_bounded (Filter.Eventually.of_forall (digitDensity_laws hp j hr side i).1)
    (measurable_of_finite _).aestronglyMeasurable 2

omit hp in
lemma measurable_hybridDigits (hr : ∀ i, 0 < MixedRadix.radices p.q i) (ε : ℕ → Bool) :
    Measurable (hybridDigits p hr ε) :=
  Measurable.of_eval (fun index => (measurable_observedDigit hr (ε index) index).comp
    (measurable_pi_apply index))

lemma measurable_hybridPoint (hr : ∀ i, 0 < MixedRadix.radices p.q i) (ε : ℕ → Bool) :
    Measurable (hybridPoint p hr ε) :=
  (MixedRadix.measurable_circleValue
    (MixedRadix.radices_ge_two hp.q_pos hp.frequency_increasing hp.frequency_divisible)).comp
      (measurable_hybridDigits hr ε)

lemma map_hybridDigits (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) (ε : ℕ → Bool) :
    (law p j).map (hybridDigits p hr ε) =
      Measure.infinitePi (fun i => (digitReference p hr i).withDensity
        (fun d => ENNReal.ofReal (digitDensity p hr j (ε i) i d))) := by
  let := coordinateLaw_isProbabilityMeasure hp j
  change (Measure.infinitePi (coordinateLaw p j)).map
    (fun ω i => observedDigit p hr (ε i) i (ω i)) = _
  rw [Measure.infinitePi_map_pi (coordinateLaw p j) (fun i => measurable_observedDigit hr (ε i) i)]
  congr 1
  funext i
  exact observedDigit_density hp j hr (ε i) i

omit hp in
@[simp] lemma hybridPoint_const (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) :
    hybridPoint p hr (fun _ => side) = point p hr side := rfl

end Invariant233.CircleCoupling

end

end OAI
