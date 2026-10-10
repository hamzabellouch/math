import Mathlib
import OAI.Probability.ThreeState.PoissonCalculus
import OAI.Probability.ThreeState.RegularCritical

namespace OAI

/-! Poisson posterior projection and entropy bounds. -/

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

noncomputable def offspringPosterior (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (Q : ProbabilityMeasure Message) (hQ : Balanced Q) : ProbabilityMeasure Message :=
  ⟨densityEvolution offspring lam h Q, densityEvolution_probability offspring lam h Q hQ⟩

lemma integral_offspringPosterior (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (Q : ProbabilityMeasure Message) (hQ : Balanced Q) (f : C(Message,ℝ)) :
    (∫ m, f m ∂(offspringPosterior offspring lam h Q hQ : Measure Message)) =
      mean offspring (fun n => ∫ m, f m ∂(degreePosterior lam h Q hQ n : Measure Message)) := by
  rw [show (offspringPosterior offspring lam h Q hQ : Measure Message) = densityEvolution offspring lam h Q by rfl,
    integral_densityEvolution_continuous offspring lam h Q hQ f]
  apply mean_congr
  intro n
  exact (integral_degreeOutput lam h Q n f f.continuous.measurable).symm

lemma posteriorMu_le_one (Q : ProbabilityMeasure Message) : posteriorMu Q ≤ 1 := by
  simpa [posteriorMu, posteriorNu] using
    integral_mono (integrable_continuous_message Q continuous_messageX) (integrable_const (1:ℝ)) messageX_le_one

lemma posteriorNu_le_one (Q : ProbabilityMeasure Message) : posteriorNu Q ≤ 1 := by
  have hp (m : Message) : (messageX m)^2≤1 := by nlinarith [messageX_nonneg m, messageX_le_one m]
  simpa [posteriorMu, posteriorNu] using
    integral_mono (integrable_continuous_message Q (continuous_messageX.pow 2)) (integrable_const (1:ℝ)) hp

lemma posteriorMu_offspring (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (Q : ProbabilityMeasure Message) (hQ : Balanced Q) :
    posteriorMu (offspringPosterior offspring lam h Q hQ) = mean offspring (fun n => posteriorMu (degreePosterior lam h Q hQ n)) :=
  integral_offspringPosterior offspring lam h Q hQ ⟨messageX,continuous_messageX⟩

lemma posteriorNu_offspring (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (Q : ProbabilityMeasure Message) (hQ : Balanced Q) :
    posteriorNu (offspringPosterior offspring lam h Q hQ) = mean offspring (fun n => posteriorNu (degreePosterior lam h Q hQ n)) := by
  unfold posteriorNu
  exact integral_offspringPosterior offspring lam h Q hQ ⟨fun m => (messageX m)^2,continuous_messageX.pow 2⟩

lemma pairCorrelation_offspring (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : Balanced Q) :
    pairCorrelation lam h Q (offspringPosterior offspring lam h Q hQ) = mean offspring (fun n => pairCorrelation lam h Q (degreePosterior lam h Q hQ n)) :=
  integral_offspringPosterior offspring lam h Q hQ ⟨pairIncrement lam h Q,continuous_pairIncrement lam h hl0 hl1 Q⟩

lemma poisson_projection_quadratic (t : ℝ) (ht : 0 ≤ t) (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : Balanced Q) (hs : SpinSymmetric Q) (s : ℝ) :
    0 ≤ posteriorMu (offspringPosterior (poissonOffspring t ht) lam h Q hQ)*s^2-
      2*(t*(lam^2*posteriorMu Q))*s+(t*(lam^2*posteriorMu Q)+t^2*(lam^2*posteriorMu Q)^2) := by
  let p := poissonOffspring t ht
  let beta := lam^2*posteriorMu Q
  let muj := fun n => posteriorMu (degreePosterior lam h Q hQ n)
  have hi : HasMean p muj := hasMean_bounded p 1 (fun n => by rw [abs_of_nonneg (posteriorMu_nonneg _)]; exact posteriorMu_le_one _)
  have h1 : HasMean p (fun n : ℕ => (n:ℝ)) := (poisson_moments t ht).hasMean
  have h2 : HasMean p (fun n : ℕ => (n:ℝ)*((n:ℝ)-1)) := (poisson_second_factorial_hasSum t ht).summable
  have hh := mean_nonneg p (fun n => degree_projection_quadratic lam h hl0 hl1 Q hQ hs n s)
  change 0 ≤ mean p (fun n => muj n*s^2-2*((n:ℝ)*beta)*s+((n:ℝ)*beta+(n:ℝ)*(n-1)*beta^2)) at hh
  have ha : HasMean p (fun n : ℕ => 2*((n:ℝ)*beta)*s) := ((h1.mul_const beta).const_mul 2).mul_const s
  rw [mean_add ((hi.mul_const _).sub ha) ((h1.mul_const _).add (h2.mul_const _)),
    mean_sub (hi.mul_const _) ha, mean_mul_const, mean_mul_const, mean_const_mul, mean_mul_const,
    mean_add (h1.mul_const _) (h2.mul_const _), mean_mul_const, mean_mul_const] at hh
  have hm1 : mean p (fun n : ℕ => (n:ℝ))=t := (poisson_moments t ht).first
  have hm2 : mean p (fun n : ℕ => (n:ℝ)*((n:ℝ)-1))=t^2 := (poisson_second_factorial_hasSum t ht).tsum_eq
  rw [hm1,hm2, ← posteriorMu_offspring (poissonOffspring t ht) lam h Q hQ] at hh
  exact hh

lemma poisson_projection (t : ℝ) (ht : 0 ≤ t) (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : Balanced Q) (hs : SpinSymmetric Q) :
    t*(lam^2*posteriorMu Q)/(1+t*(lam^2*posteriorMu Q)) ≤ posteriorMu (offspringPosterior (poissonOffspring t ht) lam h Q hQ) := by
  let x := t*(lam^2*posteriorMu Q)
  have hx : 0 ≤ x := mul_nonneg ht (mul_nonneg (sq_nonneg _) (posteriorMu_nonneg Q))
  have hd : 0 < 1+x := by positivity
  by_cases hx0 : x=0
  · change x/(1+x) ≤ _
    rw [hx0,zero_div]
    exact posteriorMu_nonneg _
  · have hxpos : 0<x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hp := poisson_projection_quadratic t ht lam h hl0 hl1 Q hQ hs
    have hdisc := discrim_le_zero (show ∀ s, 0 ≤ posteriorMu (offspringPosterior (poissonOffspring t ht) lam h Q hQ)*(s*s)+(-2*x)*s+(x+x^2) by
      intro s
      convert hp s using 1
      dsimp [x]
      ring)
    simp only [discrim] at hdisc
    change x/(1+x) ≤ _
    apply (div_le_iff₀ hd).mpr
    apply (mul_le_mul_iff_right₀ hxpos).mp
    nlinarith only [hdisc]

end ThreeState

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

lemma poissonAverage_eq_mean (f : ℕ → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    poissonAverage f t = mean (poissonOffspring t ht) f := by
  unfold poissonAverage expGenerating mean
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [poisson_mass]
  ring

lemma poissonAverage_zero (f : ℕ → ℝ) : poissonAverage f 0 = f 0 := by
  unfold poissonAverage expGenerating
  rw [neg_zero,Real.exp_zero,one_mul, tsum_eq_single 0]
  · norm_num
  · intro n hn
    simp [hn]

lemma poissonAverage_monotoneOn (f : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ n, |f n| ≤ C*((n:ℝ)+1)) (hmono : Monotone f) :
    MonotoneOn (poissonAverage f) (Set.Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (f' := poissonAverage (fun n => f (n+1)-f n))
  · intro t _
    exact (poissonAverage_hasDerivAt f C hC hf t).continuousAt.continuousWithinAt
  · intro t _
    exact (poissonAverage_hasDerivAt f C hC hf t).hasDerivWithinAt
  · intro t ht
    have ht0 : 0 ≤ t := interior_subset ht
    rw [poissonAverage_eq_mean _ t ht0]
    apply mean_nonneg
    intro n
    exact sub_nonneg.mpr (hmono (Nat.le_succ n))

lemma poisson_nu_le_fixedpoint (d : ℝ) (hd : 0 ≤ d) (t : ℝ) (ht : 0 ≤ t) (htd : t ≤ d)
    (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : IsPosteriorFixedPoint (poissonOffspring d hd) lam h Q) :
    posteriorNu (offspringPosterior (poissonOffspring t ht) lam h Q hQ.1) ≤ posteriorNu Q := by
  let f := fun n => posteriorNu (degreePosterior lam h Q hQ.1 n)
  have hf (n : ℕ) : |f n| ≤ 1*((n:ℝ)+1) := by
    rw [abs_of_nonneg (posteriorNu_nonneg _)]
    have hh := posteriorNu_le_one (degreePosterior lam h Q hQ.1 n)
    change posteriorNu (degreePosterior lam h Q hQ.1 n) ≤ _
    nlinarith [show (0:ℝ)≤n by positivity]
  have he : offspringPosterior (poissonOffspring d hd) lam h Q hQ.1 = Q := by
    apply Subtype.ext
    exact (fixedpoint_measure (poissonOffspring d hd) lam h Q hQ).symm
  have hm := poissonAverage_monotoneOn f 1 (by norm_num) hf (degree_nu_monotone lam h hl0 hl1 Q hQ.1) ht hd htd
  rw [poissonAverage_eq_mean _ t ht, poissonAverage_eq_mean _ d hd] at hm
  change mean (poissonOffspring t ht) (fun n => posteriorNu (degreePosterior lam h Q hQ.1 n)) ≤
    mean (poissonOffspring d hd) (fun n => posteriorNu (degreePosterior lam h Q hQ.1 n)) at hm
  rwa [← posteriorNu_offspring, ← posteriorNu_offspring, he] at hm

lemma poisson_correlation_hasDerivAt (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : Balanced Q) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (poissonAverage (correlationEntropy lam h Q))
      (pairCorrelation lam h Q (offspringPosterior (poissonOffspring t ht) lam h Q hQ)) t := by
  have hf (n : ℕ) : |correlationEntropy lam h Q n| ≤ edgeLogBound lam*((n:ℝ)+1) := by
    have hh := correlationEntropy_bound lam h hl0 hl1 Q hQ n
    nlinarith only [hh,edgeLogBound_nonneg lam]
  have hh := poissonAverage_hasDerivAt (correlationEntropy lam h Q) (edgeLogBound lam) (edgeLogBound_nonneg lam) hf t
  rw [poissonAverage_eq_mean _ t ht] at hh
  convert hh using 1
  rw [pairCorrelation_offspring (poissonOffspring t ht) lam h hl0 hl1 Q hQ]
  apply mean_congr
  intro n
  have he := correlationEntropy_succ lam h hl0 hl1 Q hQ n
  change _ = _ at he
  change (∫ a, pairIncrement lam h Q a ∂degreeOutput lam h Q n) = _
  linarith only [he]

end ThreeState

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

lemma poisson_increment_bound (d : ℝ) (hd : 0 ≤ d) (t : ℝ) (ht : 0 ≤ t) (htd : t ≤ d)
    (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : IsPosteriorFixedPoint (poissonOffspring d hd) lam h Q)
    (hs : SpinSymmetric Q) (he : 0 ≤ posteriorEta Q) :
    3*lam^4*(posteriorMu Q)^2*t/(1+t*lam^2*posteriorMu Q)-
      lam^4*posteriorMu Q*posteriorNu Q*Real.sqrt t ≤
      3*pairCorrelation lam h Q (offspringPosterior (poissonOffspring t ht) lam h Q hQ.1) := by
  have hm := posteriorMu_nonneg Q
  have hn := posteriorNu_nonneg Q
  let L := t*(lam^2*posteriorMu Q)/(1+t*(lam^2*posteriorMu Q))
  have hb : 0 ≤ lam^2*posteriorMu Q := mul_nonneg (sq_nonneg _) hm
  have hL : 0 ≤ L := div_nonneg (mul_nonneg ht hb) (by positivity)
  have hh := pairCorrelation_truncated lam h hl0 hl1 Q _ hQ.1 hs he
    (poisson_nu_le_fixedpoint d hd t ht htd lam h hl0 hl1 Q hQ) hL
    (poisson_projection t ht lam h hl0 hl1 Q hQ.1 hs)
  have hsqrt : Real.sqrt L ≤ lam*Real.sqrt (posteriorMu Q)*Real.sqrt t := by
    have hh := Real.sqrt_le_sqrt (div_le_self (mul_nonneg ht hb) (show 1 ≤ 1+t*(lam^2*posteriorMu Q) by nlinarith only [mul_nonneg ht hb]))
    rw [Real.sqrt_mul ht, Real.sqrt_mul (sq_nonneg lam), Real.sqrt_sq_eq_abs, abs_of_nonneg hl0] at hh
    dsimp only [L]
    nlinarith only [hh]
  have hmul := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ lam^3*Real.sqrt (posteriorMu Q)*posteriorNu Q by positivity)
  have hsq := Real.sq_sqrt hm
  have hlead : 3*lam^2*posteriorMu Q*L =
      3*lam^4*(posteriorMu Q)^2*t/(1+t*lam^2*posteriorMu Q) := by dsimp only [L]; ring
  rw [hlead] at hh
  have hloss : lam^3*Real.sqrt (posteriorMu Q)*posteriorNu Q*(lam*Real.sqrt (posteriorMu Q)*Real.sqrt t) =
      lam^4*posteriorMu Q*posteriorNu Q*Real.sqrt t := by
    calc
      _ = lam^4*(Real.sqrt (posteriorMu Q))^2*posteriorNu Q*Real.sqrt t := by ring
      _ = _ := by rw [hsq]
  rw [hloss] at hmul
  linarith only [hh, hmul]

lemma poisson_correlation_bound (d : ℝ) (hd : 0 < d) (lam : ℝ) (h : Admissible lam)
    (hl0 : 0 < lam) (hl1 : lam < 1) (hc : d*lam^2=1)
    (Q : ProbabilityMeasure Message) (hQ : IsPosteriorFixedPoint (poissonOffspring d hd.le) lam h Q)
    (hs : SpinSymmetric Q) (he : 0 ≤ posteriorEta Q) :
    3*(posteriorMu Q)^2/(2*(1+2*posteriorMu Q/3))-
      lam*posteriorMu Q*posteriorNu Q/Real.sqrt 2 ≤ 3*mean (poissonOffspring d hd.le) (correlationEntropy lam h Q) := by
  let H := poissonAverage (correlationEntropy lam h Q)
  let C := poissonAverage (fun n => correlationEntropy lam h Q (n+1)-correlationEntropy lam h Q n)
  have hderiv (t : ℝ) : HasDerivAt H (C t) t :=
    poissonAverage_hasDerivAt (correlationEntropy lam h Q) (edgeLogBound lam) (edgeLogBound_nonneg lam)
      (fun n => by
        have hh := correlationEntropy_bound lam h hl0.le hl1 Q hQ.1 n
        nlinarith only [hh,edgeLogBound_nonneg lam]) t
  have heq (t : ℝ) (ht : 0 ≤ t) : C t=pairCorrelation lam h Q (offspringPosterior (poissonOffspring t ht) lam h Q hQ.1) :=
    (hderiv t).unique (poisson_correlation_hasDerivAt lam h hl0.le hl1 Q hQ.1 t ht)
  have hh := poisson_correlation_scalar d lam (posteriorMu Q) (posteriorNu Q) hd hl0
    (posteriorMu_nonneg Q) (posteriorNu_nonneg Q) hc H C
    (by dsimp only [H]; rw [poissonAverage_zero,correlationEntropy_zero])
    (fun t _ => hderiv t) (fun t ht => by
      rw [heq t ht.1]
      exact poisson_increment_bound d hd.le t ht.1 ht.2 lam h hl0.le hl1 Q hQ hs he)
  simpa only [H,poissonAverage_eq_mean _ d hd.le] using hh

lemma poisson_entropy_bound (d : ℝ) (hd : 0 < d) (lam : ℝ) (h : Admissible lam)
    (hl0 : 0 < lam) (hl1 : lam < 1) (hc : d*lam^2=1)
    (Q : ProbabilityMeasure Message) (hQ : IsPosteriorFixedPoint (poissonOffspring d hd.le) lam h Q)
    (hs : SpinSymmetric Q) (he : 0 ≤ posteriorEta Q) :
    (1-lam^2)/2*posteriorNu Q+3*(posteriorMu Q)^2/(2*(1+2*posteriorMu Q/3))-
      lam*posteriorMu Q*posteriorNu Q/Real.sqrt 2 ≤
      (8/5:ℝ)*(∫ m, entropyJ m ∂(Q : Measure Message))^2 := by
  have hD := (poisson_moments d hd.le).hasMean
  have hD2 := (poisson_moments d hd.le).square
  have hid := entropy_identity (poissonOffspring d hd.le) lam h hl0.le hl1 Q hQ hs hD2
  have hrad := integral_entropyF_radial (poissonOffspring d hd.le) lam h hl0 hl1 Q hQ hD2
  have hcorr := poisson_correlation_bound d hd lam h hl0 hl1 hc Q hQ hs he
  have hJ := additive_entropyJ (poissonOffspring d hd.le) lam h hl0.le hl1 Q hQ hs hD
  have hfacmean : mean (poissonOffspring d hd.le) (fun n : ℕ => (n:ℝ)*((n:ℝ)-1)) = d^2 := (poisson_second_factorial_hasSum d hd.le).tsum_eq
  rw [(poisson_moments d hd.le).first, hfacmean] at hid
  rw [(poisson_moments d hd.le).first] at hJ
  have hl : lam⁻¹^2 = d := by field_simp; nlinarith only [hc]
  rw [hl] at hrad
  have hJe : (∫ m, entropyJ (edgeMessage lam h m) ∂(Q : Measure Message)) =
      lam^2*(∫ m, entropyJ m ∂(Q : Measure Message)) := by
    nlinarith only [hJ, congrArg (fun x : ℝ => x*(∫ m, entropyJ (edgeMessage lam h m) ∂(Q : Measure Message))) hc]
  rw [hJe] at hid
  have hfac : d^2*lam^4=1 := by
    calc _ = (d*lam^2)^2 := by ring
         _ = 1 := by rw [hc]; norm_num
  nlinarith only [hid,hrad,hcorr,
    congrArg (fun x : ℝ => (8/5:ℝ)*x*(∫ m, entropyJ m ∂(Q : Measure Message))^2) hfac]

end ThreeState

end OAI
