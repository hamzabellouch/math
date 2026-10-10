import Mathlib
import OAI.Probability.ThreeState.PairCorrelation

namespace OAI

/-! Posterior laws by offspring degree and monotonicity of their moments. -/

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical
open Radial (avg)

lemma continuous_integral_message {f : Message → Message → ℝ} (hf : Continuous f.uncurry)
    (Q : ProbabilityMeasure Message) : Continuous (fun a => ∫ b, f a b ∂(Q : Measure Message)) := by
  simpa only [Measure.restrict_univ] using continuous_parametric_integral_of_continuous hf isCompact_univ

lemma continuous_pairIncrement (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) : Continuous (pairIncrement lam h Q) :=
  continuous_integral_message (f := fun a b => pairNormalizer lam h a b*Real.log (pairNormalizer lam h a b)) (continuous_pairIntegrand lam h hl0 hl1) Q

noncomputable def degreePosterior (lam : ℝ) (h : Admissible lam) (Q : ProbabilityMeasure Message)
    (hQ : Balanced Q) (n : ℕ) : ProbabilityMeasure Message :=
  ⟨degreeOutput lam h Q n, degreeOutput_probability lam h Q hQ n⟩

lemma integral_iid_cons (Q : ProbabilityMeasure Message) (n : ℕ)
    (f : (Fin (n+1) → Message) → ℝ) (hf : Continuous f) :
    (∫ m, f m ∂(iidMeasure Q (n+1) : Measure (Fin (n+1) → Message))) =
      ∫ m : Fin n → Message, ∫ b, f (Fin.cons b m) ∂(Q : Measure Message)
        ∂(iidMeasure Q n : Measure (Fin n → Message)) := by
  change (∫ m, f m ∂Measure.pi (fun _ : Fin (n+1) => (Q : Measure Message))) = _
  rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => (Q : Measure Message)) 0).symm).integral_comp']
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove, cast_eq]
  apply integral_prod_symm
  exact (show Continuous (fun p : Message × (Fin n → Message) => f (Fin.cons p.1 p.2)) by
    apply hf.comp
    apply continuous_pi
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa using (continuous_fst : Continuous (Prod.fst : Message × (Fin n → Message) → Message))
    · simpa only [Fin.cons_succ, Function.comp_def] using ((continuous_apply i).comp continuous_snd : Continuous (fun p : Message × (Fin n → Message) => p.2 i))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

lemma normalizer_cons (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    {n : ℕ} (m : Fin n → Message) (b : Message) :
    normalizer lam h (Fin.cons b m) = normalizer lam h m * pairNormalizer lam h (combineMessage lam h m) b := by
  have he (i : Spin) : productWeight lam h (Fin.cons b m) i = edgeMessage lam h b i*productWeight lam h m i := by
    simp [productWeight, Fin.prod_univ_succ]
  have hn := ne_of_gt (normalizer_pos lam h hl0 hl1 m)
  change avg (productWeight lam h (Fin.cons b m)) = normalizer lam h m*avg (fun i => combineMessage lam h m i*edgeMessage lam h b i)
  simp only [Radial.avg_expand, he, combineMessage, dite_eq_right hn]
  field_simp

lemma combineMessage_cons (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    {n : ℕ} (m : Fin n → Message) (b : Message) :
    combineMessage lam h (Fin.cons b m) = pairMessage lam h hl0 hl1 (combineMessage lam h m) b := by
  apply Subtype.ext
  funext i
  have hp := ne_of_gt (normalizer_pos lam h hl0 hl1 m)
  have hp' := ne_of_gt (normalizer_pos lam h hl0 hl1 (Fin.cons b m))
  change (combineMessage lam h (Fin.cons b m)) i = (combineMessage lam h m) i*edgeMessage lam h b i / pairNormalizer lam h (combineMessage lam h m) b
  conv_lhs => rw [combineMessage, dite_eq_right hp']
  change productWeight lam h (Fin.cons b m) i/normalizer lam h (Fin.cons b m) = _
  rw [normalizer_cons lam h hl0 hl1]
  have hw := weighted_combineMessage lam h m i
  have he : productWeight lam h (Fin.cons b m) i = edgeMessage lam h b i*productWeight lam h m i := by
    simp [productWeight, Fin.prod_univ_succ]
  rw [he, ← hw]
  field_simp [hp, ne_of_gt (pairNormalizer_pos lam h hl0 hl1 _ _)]

noncomputable def pairOperator (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (f : C(Message,ℝ)) : C(Message,ℝ) :=
  ⟨fun a => ∫ b, pairNormalizer lam h a b*f (pairMessage lam h hl0 hl1 a b) ∂(Q : Measure Message),
    continuous_integral_message (f := fun a b => pairNormalizer lam h a b*f (pairMessage lam h hl0 hl1 a b)) ((continuous_pairNormalizer lam h).mul (f.continuous.comp (continuous_pairMessage lam h hl0 hl1))) Q⟩

lemma integral_degree_succ (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (n : ℕ) (f : C(Message,ℝ)) :
    (∫ m, f m ∂degreeOutput lam h Q (n+1)) =
      ∫ a, pairOperator lam h hl0 hl1 Q f a ∂degreeOutput lam h Q n := by
  rw [integral_degreeOutput lam h Q (n+1) f f.continuous.measurable,
    integral_iid_cons Q n (fun m => normalizer lam h m*f (combineMessage lam h m)) ((continuous_normalizer lam h (n+1)).mul
      (f.continuous.comp (continuous_combineMessage_positive lam h hl0 hl1 (n+1)))),
    integral_degreeOutput lam h Q n _ (pairOperator lam h hl0 hl1 Q f).continuous.measurable]
  apply integral_congr_ae
  filter_upwards with m
  simp only [normalizer_cons lam h hl0 hl1, combineMessage_cons lam h hl0 hl1, mul_assoc, pairOperator]
  exact integral_const_mul _ _

lemma correlationEntropy_zero (lam : ℝ) (h : Admissible lam) (Q : ProbabilityMeasure Message) :
    correlationEntropy lam h Q 0 = 0 := by
  simp [correlationEntropy, normalizer, productWeight]

lemma correlationEntropy_succ (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : Balanced Q) (n : ℕ) :
    correlationEntropy lam h Q (n+1) = correlationEntropy lam h Q n +
      ∫ a, pairIncrement lam h Q a ∂degreeOutput lam h Q n := by
  unfold correlationEntropy
  rw [integral_iid_cons Q n (fun m => normalizer lam h m*Real.log (normalizer lam h m)) ((continuous_normalizer lam h (n+1)).mul (continuous_log_normalizer lam h hl0 hl1 (n+1)))]
  have he (m : Fin n → Message) :
      (∫ b, normalizer lam h (Fin.cons b m)*Real.log (normalizer lam h (Fin.cons b m)) ∂(Q : Measure Message)) =
        normalizer lam h m*Real.log (normalizer lam h m)+normalizer lam h m*pairIncrement lam h Q (combineMessage lam h m) := by
    let a := combineMessage lam h m
    have hpn : Continuous (fun b => pairNormalizer lam h a b) :=
      (continuous_pairNormalizer lam h).comp (continuous_const.prodMk continuous_id)
    have hpi : Continuous (fun b => pairNormalizer lam h a b*Real.log (pairNormalizer lam h a b)) :=
      (continuous_pairIntegrand lam h hl0 hl1).comp (continuous_const.prodMk continuous_id)
    have hfun (b : Message) : normalizer lam h (Fin.cons b m)*Real.log (normalizer lam h (Fin.cons b m)) =
        (normalizer lam h m*Real.log (normalizer lam h m))*pairNormalizer lam h a b+
          normalizer lam h m*(pairNormalizer lam h a b*Real.log (pairNormalizer lam h a b)) := by
      rw [normalizer_cons lam h hl0 hl1, Real.log_mul (ne_of_gt (normalizer_pos lam h hl0 hl1 m))
        (ne_of_gt (pairNormalizer_pos lam h hl0 hl1 _ _))]
      dsimp only [a]
      ring
    simp_rw [hfun]
    rw [integral_add ((integrable_continuous_message Q hpn).const_mul _) ((integrable_continuous_message Q hpi).const_mul _),
      integral_const_mul, integral_const_mul, integral_pairNormalizer lam h Q hQ, mul_one]
    rfl
  simp_rw [he]
  rw [integral_add]
  · rw [integral_degreeOutput lam h Q n _ (continuous_pairIncrement lam h hl0 hl1 Q).measurable]
  · exact ((continuous_normalizer lam h n).mul (continuous_log_normalizer lam h hl0 hl1 n)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact ((continuous_normalizer lam h n).mul ((continuous_pairIncrement lam h hl0 hl1 Q).comp
      (continuous_combineMessage_positive lam h hl0 hl1 n))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end ThreeState
namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical
open Radial (avg)

lemma messageX_sq_tangent (a c : Message) :
    (messageX a)^2+2*messageX a*avg (fun i => (a i-1)*(c i-a i)) ≤ (messageX c)^2 := by
  let D := avg (fun i => (c i-a i)^2)/2
  have hD : 0 ≤ D := div_nonneg (avg_nonneg (fun i => sq_nonneg (c i-a i))) (by norm_num)
  have he : messageX c-messageX a = avg (fun i => (a i-1)*(c i-a i))+D := by
    dsimp only [messageX, Radial.momentX, messageDeviation, D]
    simp only [Radial.avg_expand]
    ring
  have hm := mul_nonneg (messageX_nonneg a) hD
  have hx := congrArg (fun t : ℝ => 2*messageX a*t) he
  nlinarith only [hx, hm, sq_nonneg (messageX c-messageX a)]

lemma integral_weighted_pair_deviation (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : Balanced Q) (a : Message) (i : Spin) :
    (∫ b, pairNormalizer lam h a b*(pairMessage lam h hl0 hl1 a b i-a i) ∂(Q : Measure Message)) = 0 := by
  have he (b : Message) : pairNormalizer lam h a b*(pairMessage lam h hl0 hl1 a b i-a i) =
      a i*(edgeMessage lam h b i-pairNormalizer lam h a b) := by
    change pairNormalizer lam h a b*(a i*edgeMessage lam h b i/pairNormalizer lam h a b-a i) = _
    field_simp [ne_of_gt (pairNormalizer_pos lam h hl0 hl1 a b)]
  simp_rw [he]
  have hi : Integrable (fun b => edgeMessage lam h b i) (Q : Measure Message) :=
    integrable_continuous_message Q (((continuous_apply i).comp continuous_subtype_val).comp (continuous_edgeMessage lam h))
  have hp : Integrable (fun b => pairNormalizer lam h a b) (Q : Measure Message) :=
    integrable_continuous_message Q ((continuous_pairNormalizer lam h).comp (continuous_const.prodMk continuous_id))
  rw [integral_const_mul, integral_sub hi hp, integral_edgeMessage lam h Q hQ,
    integral_pairNormalizer lam h Q hQ]
  ring

lemma pairOperator_square_lower (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : Balanced Q) (a : Message) :
    (messageX a)^2 ≤ pairOperator lam h hl0 hl1 Q ⟨fun m => (messageX m)^2, continuous_messageX.pow 2⟩ a := by
  let N : Message → ℝ := fun b => pairNormalizer lam h a b
  let P : Message → Message := fun b => pairMessage lam h hl0 hl1 a b
  let G : Message → Spin → ℝ := fun b i => N b*(P b i-a i)
  have hn : Continuous N := (continuous_pairNormalizer lam h).comp (continuous_const.prodMk continuous_id)
  have hp : Continuous P := (continuous_pairMessage lam h hl0 hl1).comp (continuous_const.prodMk continuous_id)
  have hg (i : Spin) : Continuous (fun b => G b i) := hn.mul ((((continuous_apply i).comp continuous_subtype_val).comp hp).sub continuous_const)
  have hl : Continuous (fun b => N b*(messageX a)^2+2*messageX a*avg (fun i => (a i-1)*G b i)) :=
    (hn.mul continuous_const).add (continuous_const.mul (continuous_avg _ (fun i => continuous_const.mul (hg i))))
  have hr : Continuous (fun b => N b*(messageX (P b))^2) := hn.mul ((continuous_messageX.comp hp).pow 2)
  have hin (b : Message) : N b*(messageX a)^2+2*messageX a*avg (fun i => (a i-1)*G b i) ≤ N b*(messageX (P b))^2 := by
    have hh := mul_le_mul_of_nonneg_left (messageX_sq_tangent a (P b)) (pairNormalizer_pos lam h hl0 hl1 a b).le
    convert hh using 1
    first | rfl | (simp only [G, Radial.avg_expand]; ring)
  have hh := integral_mono (integrable_continuous_message Q hl) (integrable_continuous_message Q hr) hin
  have hil : Integrable (fun b => N b*(messageX a)^2) (Q : Measure Message) := integrable_continuous_message Q (hn.mul continuous_const)
  have hig : Integrable (fun b => 2*messageX a*avg (fun i => (a i-1)*G b i)) (Q : Measure Message) :=
    integrable_continuous_message Q (continuous_const.mul (continuous_avg _ (fun i => continuous_const.mul (hg i))))
  rw [integral_add hil hig, integral_mul_const, integral_const_mul,
    integral_avg _ _ (fun i => (integrable_continuous_message Q (hg i)).const_mul _)] at hh
  simp only [G,N,P, integral_const_mul, integral_weighted_pair_deviation lam h hl0 hl1 Q hQ,
    integral_pairNormalizer lam h Q hQ, mul_zero, avg, Finset.sum_const_zero, zero_div, one_mul, add_zero] at hh
  exact hh

lemma degree_nu_monotone (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : Balanced Q) :
    Monotone (fun n => posteriorNu (degreePosterior lam h Q hQ n)) := by
  apply monotone_nat_of_le_succ
  intro n
  change (∫ m, (messageX m)^2 ∂degreeOutput lam h Q n) ≤ ∫ m, (messageX m)^2 ∂degreeOutput lam h Q (n+1)
  have he : (∫ m, (messageX m)^2 ∂degreeOutput lam h Q (n+1)) =
      ∫ a, pairOperator lam h hl0 hl1 Q ⟨fun m => (messageX m)^2, continuous_messageX.pow 2⟩ a ∂degreeOutput lam h Q n := by
    exact integral_degree_succ lam h hl0 hl1 Q n ⟨fun m => (messageX m)^2, continuous_messageX.pow 2⟩
  rw [he]
  let := degreeOutput_probability lam h Q hQ n
  apply integral_mono
  · exact (continuous_messageX.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (pairOperator lam h hl0 hl1 Q ⟨fun m => (messageX m)^2, continuous_messageX.pow 2⟩).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact pairOperator_square_lower lam h hl0 hl1 Q hQ

end ThreeState

end OAI
