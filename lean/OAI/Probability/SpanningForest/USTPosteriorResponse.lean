import OAI.Probability.SpanningForest.USTFiniteTilt
import OAI.Probability.SpanningForest.FiniteUSTProbability
import OAI.Probability.SpanningForest.PosteriorTiltLimit

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Problem336.USTResponse

def extendMarks (h : EdgeCode → ℝ) (p : ℕ × ℕ) : ℝ :=
  if hp : p.1 < p.2 then h ⟨p, hp⟩ else 0

@[simp] lemma extendMarks_coe (h : EdgeCode → ℝ) (e : EdgeCode) :
    extendMarks h e.1 = h e := by simp [extendMarks, e.2]

lemma bit_finiteTreeConfiguration (T : Finset (ℕ × ℕ)) (e : EdgeCode) :
    TiltLimit.bit (finiteTreeConfiguration T e) = if e.1 ∈ T then 1 else 0 := by
  classical
  by_cases he : e.1 ∈ T <;> simp [TiltLimit.bit, finiteTreeConfiguration, he]

private lemma sum_restrict_support (K T S : Finset (ℕ × ℕ))
    (hT : T ⊆ K) (h : (ℕ × ℕ) → ℝ) :
    (∑ p ∈ K, (if p ∈ S then h p else 0) * (if p ∈ T then 1 else 0)) =
      ∑ p ∈ S, h p * (if p ∈ T then 1 else 0) := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hT]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  simp only [Finset.filter_mem_eq_inter, Finset.inter_comm]

lemma finiteEnergy_eq_observationField (K : FiniteSubgraphCode)
    (T : TreeSample K) (S : Finset EdgeCode) (h : EdgeCode → ℝ) :
    TiltLimit.finiteEnergy S h (finiteTreeConfiguration T.1) =
      ∑ f : FiniteEdge K,
        observationField K (S.image Subtype.val) 0 (extendMarks h) f * indicator K T f := by
  classical
  simp only [observationField, zero_div, sub_zero, indicator]
  rw [← Finset.sum_subtype K.2 (fun _ => Iff.rfl)
    (fun p => (if p ∈ S.image Subtype.val then extendMarks h p else 0) *
      (if p ∈ T.1 then (1 : ℝ) else 0))]
  rw [sum_restrict_support K.2 T.1 (S.image Subtype.val) (tree_property K T).1]
  rw [Finset.sum_image]
  · simp only [TiltLimit.finiteEnergy, extendMarks_coe, bit_finiteTreeConfiguration]
  · intro a _ b _ hab
    exact Subtype.val_injective hab

lemma exp_finiteEnergy_eq_weight (K : FiniteSubgraphCode)
    (T : TreeSample K) (S : Finset EdgeCode) (h : EdgeCode → ℝ) :
    Real.exp (TiltLimit.finiteEnergy S h (finiteTreeConfiguration T.1)) =
      weight K (observationField K (S.image Subtype.val) 0 (extendMarks h)) T := by
  rw [finiteEnergy_eq_observationField]
  rfl

lemma tiltedMean_finiteUSTProbability (K : FiniteSubgraphCode)
    (hne : (spanningTrees K).Nonempty)
    (energy obs : EdgeConfiguration → ℝ) :
    TiltLimit.tiltedMean (finiteUSTProbability K hne) energy obs =
      (∑ T : TreeSample K, obs (finiteTreeConfiguration T.1) *
        Real.exp (energy (finiteTreeConfiguration T.1))) /
      (∑ T : TreeSample K, Real.exp (energy (finiteTreeConfiguration T.1))) := by
  have hc : ((spanningTrees K).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hne
  unfold TiltLimit.tiltedMean
  change (∫ X, obs X * Real.exp (energy X) ∂finiteUSTMeasure K) /
    (∫ X, Real.exp (energy X) ∂finiteUSTMeasure K) = _
  rw [integral_finiteUSTMeasure, integral_finiteUSTMeasure,
    div_div_div_cancel_right₀ hc]
  congr 1 <;> exact Finset.sum_subtype (spanningTrees K) (fun _ => Iff.rfl) _

lemma finiteTiltMean_eq_weight_ratio (K : FiniteSubgraphCode)
    (hne : (spanningTrees K).Nonempty) (S : Finset EdgeCode)
    (h : EdgeCode → ℝ) (e : EdgeCode) :
    TiltLimit.finiteTiltMean (finiteUSTProbability K hne) S h e =
      (∑ T : TreeSample K, TiltLimit.bit (finiteTreeConfiguration T.1 e) *
        weight K (observationField K (S.image Subtype.val) 0 (extendMarks h)) T) /
      partition K (observationField K (S.image Subtype.val) 0 (extendMarks h)) := by
  rw [TiltLimit.finiteTiltMean, tiltedMean_finiteUSTProbability]
  simp_rw [exp_finiteEnergy_eq_weight]
  rfl

theorem finiteTiltMean_eq_finiteTilt (K : FiniteSubgraphCode)
    (hne : (spanningTrees K).Nonempty) (S : Finset EdgeCode)
    (h : EdgeCode → ℝ) (e : EdgeCode) :
    TiltLimit.finiteTiltMean (finiteUSTProbability K hne) S h e =
      finiteTilt K (S.image Subtype.val) 0 (extendMarks h) e.1 := by
  rw [finiteTiltMean_eq_weight_ratio]
  by_cases he : e.1 ∈ K.2
  · rw [finiteTilt_of_mem K _ 0 _ e.1 he, inclusion_eq_ratio]
    congr 1
    apply Finset.sum_congr rfl
    intro T _
    simp [bit_finiteTreeConfiguration, indicator, mul_comm]
  · rw [finiteTilt_of_not_mem K _ 0 _ e.1 he]
    have hz (T : TreeSample K) : TiltLimit.bit (finiteTreeConfiguration T.1 e) = 0 := by
      rw [bit_finiteTreeConfiguration, ite_eq_right]
      exact fun ht => he ((tree_property K T).1 ht)
    simp_rw [hz, zero_mul]
    simp

theorem finiteUST_posterior_response_of_response (K : FiniteSubgraphCode)
    (hne : (spanningTrees K).Nonempty)
    (hresponse : ∀ (a b : FiniteEdge K → ℝ) (e : FiniteEdge K) (D : ℝ),
      0 ≤ D → (∀ f, |b f - a f| ≤ D) →
        |inclusion K b e - inclusion K a e| ≤ D / 2)
    (S : Finset EdgeCode) (h h' : EdgeCode → ℝ) (e : EdgeCode)
    (D : ℝ) (hD : 0 ≤ D) (hh : ∀ f ∈ S, |h' f - h f| ≤ D) :
    |TiltLimit.finiteTiltMean (finiteUSTProbability K hne) S h' e -
      TiltLimit.finiteTiltMean (finiteUSTProbability K hne) S h e| ≤ D / 2 := by
  rw [finiteTiltMean_eq_finiteTilt, finiteTiltMean_eq_finiteTilt]
  apply finiteTilt_response_of_response K hresponse (S.image Subtype.val) 0
    (extendMarks h) (extendMarks h') e.1 D hD
  intro p hp
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hp
  simpa only [extendMarks_coe] using hh f hf

theorem finiteUST_posterior_response (K : FiniteSubgraphCode)
    (hne : (spanningTrees K).Nonempty)
    (hneg : ∀ h e f, e ≠ f → edgeCovariance K h e f ≤ 0)
    (S : Finset EdgeCode) (h h' : EdgeCode → ℝ) (e : EdgeCode)
    (D : ℝ) (hD : 0 ≤ D) (hh : ∀ f ∈ S, |h' f - h f| ≤ D) :
    |TiltLimit.finiteTiltMean (finiteUSTProbability K hne) S h' e -
      TiltLimit.finiteTiltMean (finiteUSTProbability K hne) S h e| ≤ D / 2 := by
  rw [finiteTiltMean_eq_finiteTilt, finiteTiltMean_eq_finiteTilt]
  apply finiteTilt_response K (S.image Subtype.val) hne hneg 0
    (extendMarks h) (extendMarks h') e.1 D hD
  intro p hp
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hp
  simpa only [extendMarks_coe] using hh f hf

theorem finiteUST_limit_posterior_response {J : Type*} {l : Filter J} [l.NeBot]
    (K : J → FiniteSubgraphCode) (hne : ∀ j, (spanningTrees (K j)).Nonempty)
    (hneg : ∀ j h e f, e ≠ f → edgeCovariance (K j) h e f ≤ 0)
    (μ : ProbabilityMeasure EdgeConfiguration)
    (hμ : Filter.Tendsto (fun j => finiteUSTProbability (K j) (hne j)) l (nhds μ))
    (S : Finset EdgeCode) (h h' : EdgeCode → ℝ) (e : EdgeCode)
    (D : ℝ) (hD : 0 ≤ D) (hh : ∀ f ∈ S, |h' f - h f| ≤ D) :
    |TiltLimit.finiteTiltMean μ S h' e - TiltLimit.finiteTiltMean μ S h e| ≤ D / 2 := by
  exact TiltLimit.finiteTiltMean_response_bound_of_tendsto hμ S h' h e
    (Filter.Eventually.of_forall fun j =>
      finiteUST_posterior_response (K j) (hne j) (hneg j) S h h' e D hD hh)

end Problem336.USTResponse

end

end OAI
