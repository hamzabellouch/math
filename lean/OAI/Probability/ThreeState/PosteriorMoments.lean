import Mathlib
import OAI.Probability.ThreeState.EntropyRecursion
import OAI.Probability.ThreeState.Resolvents

namespace OAI

/-! Posterior deviation moments and positive-channel estimates. -/

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical
open Radial (avg)

noncomputable def messageDeviation (m : Message) : Spin → ℝ := fun i => m i-1
noncomputable def messageX (m : Message) : ℝ := Radial.momentX (messageDeviation m)
noncomputable def messageY (m : Message) : ℝ := Radial.momentY (messageDeviation m)

lemma avg_messageDeviation (m : Message) : avg (messageDeviation m) = 0 := by
  have hh := average_message m
  simp only [messageDeviation, Radial.avg_expand] at *
  linarith

lemma messageX_nonneg (m : Message) : 0 ≤ messageX m := Radial.momentX_nonneg _

lemma messageX_le_one (m : Message) : messageX m ≤ 1 := by
  have hi (i : Spin) : (m i)^2 ≤ 3*m i := by nlinarith [Message.nonneg m i, Message.le_three m i]
  have hh := average_message m
  simp only [messageX, messageDeviation, Radial.momentX, Radial.avg_expand] at *
  nlinarith [hi 0,hi 1,hi 2]

lemma continuous_messageX : Continuous messageX := by
  change Continuous (fun m : Message => avg (fun i => (m i-1)^2)/2)
  exact (continuous_avg _ (fun i => (((continuous_apply i).comp continuous_subtype_val).sub continuous_const).pow 2)).div_const 2

lemma continuous_messageY : Continuous messageY := by
  change Continuous (fun m : Message => avg (fun i => (m i-1)^3)/2)
  exact (continuous_avg _ (fun i => (((continuous_apply i).comp continuous_subtype_val).sub continuous_const).pow 3)).div_const 2

lemma integrable_continuous_message (Q : ProbabilityMeasure Message) {f : Message → ℝ} (hf : Continuous f) :
    Integrable f (Q : Measure Message) := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma entropyJ_functionJ (m : Message) : entropyJ m = Radial.functionJ (messageDeviation m) := by
  simp [entropyJ, Radial.functionJ, messageDeviation, mLog]

lemma messageDeviation_edge (lam : ℝ) (h : Admissible lam) (m : Message) :
    messageDeviation (edgeMessage lam h m) = fun i => lam*messageDeviation m i := by
  funext i
  simp [messageDeviation, edgeMessage]

lemma entropyJ_nonneg (m : Message) (hp : ∀ i, 0 < m i) : 0 ≤ entropyJ m := by
  apply div_nonneg (avg_nonneg _) (by norm_num)
  intro i
  dsimp only [mLog]
  rcases le_total (m i) 1 with hi | hi
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (Real.log_nonpos (le_of_lt (hp i)) hi)
  · exact mul_nonneg (by linarith) (Real.log_nonneg hi)

 

noncomputable def messageA (m : Message) : ℝ := 2*entropyJ m-2*messageX m+messageY m
noncomputable def messageQ (lam : ℝ) (h : Admissible lam) (m : Message) : ℝ :=
  (lam^3*entropyJ m-entropyJ (edgeMessage lam h m)+lam^2*(1-lam)*messageX m)/(lam^3*(1-lam))

lemma messageA_eq_resolvent (m : Message) (hp : ∀ i, 0 < m i) :
    messageA m = Radial.resolventA (messageDeviation m) := by
  rw [Radial.resolventA_identity _ (by simpa [messageDeviation] using hp)]
  simp [messageA, entropyJ_functionJ, messageX, messageY]

lemma messageQ_eq_resolvent (lam : ℝ) (h : Admissible lam) (hl0 : 0 < lam) (hl1 : lam < 1)
    (m : Message) (hp : ∀ i, 0 < m i) :
    messageQ lam h m = Radial.resolventQ (messageDeviation m) lam := by
  apply (div_eq_iff (ne_of_gt (mul_pos (pow_pos hl0 _) (sub_pos.mpr hl1)))).mpr
  have hh := Radial.resolventQ_identity (messageDeviation m) (by simpa [messageDeviation] using hp) lam hl0.le hl1.le
  simp only [entropyJ_functionJ, messageDeviation_edge, messageX]
  linarith only [hh]

lemma messageA_lower (m : Message) (hp : ∀ i, 0 < m i) :
    (37/27:ℝ)*(messageX m)^2 ≤ messageA m := by
  rw [messageA_eq_resolvent m hp]
  exact Radial.resolventA_lower _ (avg_messageDeviation m) (by simpa [messageDeviation] using hp)

lemma messageQ_lower (lam : ℝ) (h : Admissible lam) (hl0 : 0 < lam) (hl1 : lam < 1)
    (m : Message) (hp : ∀ i, 0 < m i) : messageA m/(2+lam) ≤ messageQ lam h m := by
  rw [messageA_eq_resolvent m hp, messageQ_eq_resolvent lam h hl0 hl1 m hp]
  exact Radial.resolventQ_lower _ (avg_messageDeviation m) (by simpa [messageDeviation] using hp) lam hl0.le hl1.le

lemma messageY_upper (m : Message) : messageY m ≤ messageX m*Real.sqrt (messageX m) := by
  have hh := (Radial.momentY_sqrt_bound _ (avg_messageDeviation m)).2
  change messageY m ≤ (Real.sqrt (messageX m))^3 at hh
  have he : (Real.sqrt (messageX m))^3 = messageX m*Real.sqrt (messageX m) := by
    calc
      (Real.sqrt (messageX m))^3 = (Real.sqrt (messageX m))^2*Real.sqrt (messageX m) := by ring
      _ = _ := by rw [Real.sq_sqrt (messageX_nonneg m)]
  rwa [he] at hh

lemma integral_continuous_cauchy (Q : ProbabilityMeasure Message) (f g : Message → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    (∫ m, f m*g m ∂(Q : Measure Message))^2 ≤
      (∫ m, (f m)^2 ∂(Q : Measure Message))*(∫ m, (g m)^2 ∂(Q : Measure Message)) := by
  have hf2 : Integrable (fun m => (f m)^2) (Q : Measure Message) := integrable_continuous_message Q (hf.pow 2)
  have hg2 : Integrable (fun m => (g m)^2) (Q : Measure Message) := integrable_continuous_message Q (hg.pow 2)
  have hfg : Integrable (fun m => f m*g m) (Q : Measure Message) := integrable_continuous_message Q (hf.mul hg)
  have hp (t : ℝ) : 0 ≤
      (∫ m, (f m)^2 ∂(Q : Measure Message))*(t*t)+
      (-2*(∫ m, f m*g m ∂(Q : Measure Message)))*t+(∫ m, (g m)^2 ∂(Q : Measure Message)) := by
    have hnon : 0 ≤ ∫ m, (t*f m-g m)^2 ∂(Q : Measure Message) := integral_nonneg (fun message => sq_nonneg (t*f message-g message))
    have he (m : Message) : (t*f m-g m)^2 = t^2*(f m)^2+(-2*t)*(f m*g m)+(g m)^2 := by ring
    simp_rw [he] at hnon
    have his : Integrable (fun m => t^2*(f m)^2+(-2*t)*(f m*g m)) (Q : Measure Message) := (hf2.const_mul _).add (hfg.const_mul _)
    rw [integral_add his hg2,
      integral_add (hf2.const_mul _) (hfg.const_mul _), integral_const_mul, integral_const_mul] at hnon
    nlinarith only [hnon]
  have hh := discrim_le_zero hp
  simp only [discrim] at hh
  nlinarith only [hh]

noncomputable def posteriorMu (Q : ProbabilityMeasure Message) : ℝ := ∫ m, messageX m ∂(Q : Measure Message)
noncomputable def posteriorNu (Q : ProbabilityMeasure Message) : ℝ := ∫ m, (messageX m)^2 ∂(Q : Measure Message)
noncomputable def posteriorEta (Q : ProbabilityMeasure Message) : ℝ := ∫ m, messageY m ∂(Q : Measure Message)

lemma posteriorMu_nonneg (Q : ProbabilityMeasure Message) : 0 ≤ posteriorMu Q := integral_nonneg messageX_nonneg
lemma posteriorNu_nonneg (Q : ProbabilityMeasure Message) : 0 ≤ posteriorNu Q := integral_nonneg (fun message => sq_nonneg (messageX message))

lemma posteriorMu_sq_le (Q : ProbabilityMeasure Message) : (posteriorMu Q)^2 ≤ posteriorNu Q := by
  have hh := integral_continuous_cauchy Q messageX (fun _ => 1) continuous_messageX continuous_const
  simpa [posteriorMu, posteriorNu] using hh

lemma posteriorEta_upper (Q : ProbabilityMeasure Message) : posteriorEta Q ≤ Real.sqrt (posteriorMu Q*posteriorNu Q) := by
  let r : Message → ℝ := fun m => Real.sqrt (messageX m)
  have hc : Continuous r := continuous_messageX.sqrt
  have hh := integral_continuous_cauchy Q r messageX hc continuous_messageX
  have hs : ∀ m, (r m)^2 = messageX m := fun m => Real.sq_sqrt (messageX_nonneg m)
  simp_rw [hs] at hh
  have hi : Integrable (fun m => messageX m*r m) (Q : Measure Message) := integrable_continuous_message Q (continuous_messageX.mul hc)
  have h0 : 0 ≤ ∫ m, messageX m*r m ∂(Q : Measure Message) := integral_nonneg (fun m => mul_nonneg (messageX_nonneg m) (Real.sqrt_nonneg _))
  have he : (∫ m, messageX m*r m ∂(Q : Measure Message)) ≤ Real.sqrt (posteriorMu Q*posteriorNu Q) := by
    apply (Real.le_sqrt h0 (mul_nonneg (posteriorMu_nonneg Q) (posteriorNu_nonneg Q))).mpr
    simpa only [posteriorMu, posteriorNu, mul_comm] using hh
  exact (integral_mono (integrable_continuous_message Q continuous_messageY) hi messageY_upper).trans he

lemma integrable_messageA (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : IsPosteriorFixedPoint offspring lam h Q)
    (hD : HasMean offspring (fun n : ℕ => (n:ℝ))) : Integrable messageA (Q : Measure Message) := by
  exact (((integrable_entropyJ_fixedpoint offspring lam h hl0 hl1 Q hQ hD).const_mul 2).sub
    ((integrable_continuous_message Q continuous_messageX).const_mul 2)).add
      (integrable_continuous_message Q continuous_messageY)

lemma integrable_messageQ (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : IsPosteriorFixedPoint offspring lam h Q)
    (hD : HasMean offspring (fun n : ℕ => (n:ℝ))) : Integrable (messageQ lam h) (Q : Measure Message) := by
  exact ((((integrable_entropyJ_fixedpoint offspring lam h hl0 hl1 Q hQ hD).const_mul _).sub
    (integrable_continuous_message Q (continuous_entropyJ_edge lam h hl0 hl1))).add
      ((integrable_continuous_message Q continuous_messageX).const_mul _)).div_const _

lemma integral_messageA (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : IsPosteriorFixedPoint offspring lam h Q)
    (hD : HasMean offspring (fun n : ℕ => (n:ℝ))) :
    (∫ m, messageA m ∂(Q : Measure Message)) = 2*(∫ m, entropyJ m ∂(Q : Measure Message))-2*posteriorMu Q+posteriorEta Q := by
  have hj := integrable_entropyJ_fixedpoint offspring lam h hl0 hl1 Q hQ hD
  have hx := integrable_continuous_message Q continuous_messageX
  have hy := integrable_continuous_message Q continuous_messageY
  change (∫ m, 2*entropyJ m-2*messageX m+messageY m ∂(Q : Measure Message)) = _
  have his : Integrable (fun m => 2*entropyJ m-2*messageX m) (Q : Measure Message) := (hj.const_mul 2).sub (hx.const_mul 2)
  rw [integral_add his hy, integral_sub (hj.const_mul 2) (hx.const_mul 2), integral_const_mul, integral_const_mul]
  rfl

lemma integral_messageQ (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) (hl0 : 0 < lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : IsPosteriorFixedPoint offspring lam h Q) (hs : SpinSymmetric Q)
    (hD : HasMean offspring (fun n : ℕ => (n:ℝ))) (hc : mean offspring (fun n : ℕ => (n:ℝ))*lam^2 = 1) :
    (∫ m, entropyJ m ∂(Q : Measure Message)) = posteriorMu Q-lam*(∫ m, messageQ lam h m ∂(Q : Measure Message)) := by
  have hj := integrable_entropyJ_fixedpoint offspring lam h hl0.le hl1 Q hQ hD
  have hje := integrable_continuous_message Q (continuous_entropyJ_edge lam h hl0.le hl1)
  have hx := integrable_continuous_message Q continuous_messageX
  have hadd := additive_entropyJ offspring lam h hl0.le hl1 Q hQ hs hD
  have he : (∫ m, entropyJ (edgeMessage lam h m) ∂(Q : Measure Message)) =
      lam^2*(∫ m, entropyJ m ∂(Q : Measure Message)) := by nlinarith [congrArg (fun x : ℝ => x*(∫ m, entropyJ (edgeMessage lam h m) ∂(Q : Measure Message))) hc]
  simp only [messageQ]
  have his : Integrable (fun m => lam^3*entropyJ m-entropyJ (edgeMessage lam h m)) (Q : Measure Message) := (hj.const_mul _).sub hje
  rw [integral_div, integral_add his (hx.const_mul _),
    integral_sub (hj.const_mul _) hje, integral_const_mul, integral_const_mul, he]
  dsimp only [posteriorMu]
  field_simp [ne_of_gt hl0, ne_of_gt (sub_pos.mpr hl1)]
  ring

lemma positive_moment_estimates (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) (hl0 : 0 < lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : IsPosteriorFixedPoint offspring lam h Q) (hs : SpinSymmetric Q)
    (hD : HasMean offspring (fun n : ℕ => (n:ℝ))) (hc : mean offspring (fun n : ℕ => (n:ℝ))*lam^2 = 1) :
    let q : ℝ := (37/27:ℝ)/(2+lam)
    let c : ℝ := (37/27:ℝ)+2*lam*q
    0 ≤ (∫ m, entropyJ m ∂(Q : Measure Message)) ∧
    (∫ m, entropyJ m ∂(Q : Measure Message)) ≤ posteriorMu Q-lam*q*posteriorNu Q ∧
    c*posteriorNu Q ≤ posteriorEta Q ∧ posteriorEta Q ≤ Real.sqrt (posteriorMu Q*posteriorNu Q) := by
  dsimp only
  have hp := positive_fixedpoint offspring lam h hl0.le hl1 Q hQ
  have hiA := integrable_messageA offspring lam h hl0.le hl1 Q hQ hD
  have hiQ := integrable_messageQ offspring lam h hl0.le hl1 Q hQ hD
  have hA : (37/27:ℝ)*posteriorNu Q ≤ ∫ m, messageA m ∂(Q : Measure Message) := by
    have hh := integral_mono_ae ((integrable_continuous_message Q (continuous_messageX.pow 2)).const_mul (37/27:ℝ)) hiA
      (hp.mono (fun m hm => messageA_lower m hm))
    simpa only [integral_const_mul, posteriorNu, Pi.pow_apply] using hh
  have hQ' : (∫ m, messageA m ∂(Q : Measure Message))/(2+lam) ≤ ∫ m, messageQ lam h m ∂(Q : Measure Message) := by
    have hh := integral_mono_ae (hiA.div_const (2+lam)) hiQ
      (hp.mono (fun m hm => messageQ_lower lam h hl0 hl1 m hm))
    simpa only [integral_div] using hh
  have hQl : (37/27:ℝ)/(2+lam)*posteriorNu Q ≤ ∫ m, messageQ lam h m ∂(Q : Measure Message) := by
    have hh := (div_le_div_of_nonneg_right hA (by linarith : 0 ≤ 2+lam)).trans hQ'
    simpa only [div_mul_eq_mul_div] using hh
  have hJ := integral_messageQ offspring lam h hl0 hl1 Q hQ hs hD hc
  have hAi := integral_messageA offspring lam h hl0.le hl1 Q hQ hD
  refine ⟨integral_nonneg_of_ae (hp.mono (fun m hm => entropyJ_nonneg m hm)), ?_, ?_, posteriorEta_upper Q⟩
  · nlinarith only [hQl, hJ, hl0]
  · nlinarith only [hQl, hJ, hAi, hA, hl0]

end ThreeState

end OAI
