import Mathlib
import OAI.Probability.ThreeState.Projection
import OAI.Probability.ThreeState.ScalarBounds

namespace OAI

/-! Entropy bounds and non-reconstruction at the positive regular-tree threshold. -/

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

lemma regular_fixedpoint_degree_nu (b : ℕ) (lam : ℝ) (h : Admissible lam)
    (Q : ProbabilityMeasure Message) (hQ : IsPosteriorFixedPoint (PMF.pure b) lam h Q) :
    posteriorNu (degreePosterior lam h Q hQ.1 b) = posteriorNu Q := by
  have hh := hQ.2 ⟨fun m => (messageX m)^2, continuous_messageX.pow 2⟩
  rw [mean_pure] at hh
  change (∫ m, (messageX m)^2 ∂(Q : Measure Message)) =
    ∫ m : Fin b → Message, normalizer lam h m*(messageX (combineMessage lam h m))^2 ∂(iidMeasure Q b : Measure (Fin b → Message)) at hh
  change (∫ m, (messageX m)^2 ∂degreeOutput lam h Q b) = _
  rw [integral_degreeOutput lam h Q b (fun m => (messageX m)^2) (continuous_messageX.pow 2).measurable]
  exact hh.symm

lemma partial_nu_le_regular (b : ℕ) (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : IsPosteriorFixedPoint (PMF.pure b) lam h Q) {j : ℕ} (hj : j ≤ b) :
    posteriorNu (degreePosterior lam h Q hQ.1 j) ≤ posteriorNu Q := by
  rw [← regular_fixedpoint_degree_nu b lam h Q hQ]
  exact degree_nu_monotone lam h hl0 hl1 Q hQ.1 hj

lemma correlationEntropy_sum (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : Balanced Q) (b : ℕ) :
    correlationEntropy lam h Q b =
      ∑ j ∈ Finset.range b, pairCorrelation lam h Q (degreePosterior lam h Q hQ j) := by
  induction b with
  | zero => simp [correlationEntropy_zero]
  | succ b ih =>
    rw [Finset.sum_range_succ, ← ih]
    have hh := correlationEntropy_succ lam h hl0 hl1 Q hQ b
    change correlationEntropy lam h Q (b+1) = correlationEntropy lam h Q b +
      pairCorrelation lam h Q (degreePosterior lam h Q hQ b) at hh
    exact hh

lemma scalar_sqrt_projection_bound {j beta : ℝ} (hj : 1 ≤ j) (hb : 0 ≤ beta) :
    Real.sqrt (j*beta/(1+(j-1)*beta)) ≤ Real.sqrt (j*beta) := by
  apply Real.sqrt_le_sqrt
  have hd : 1 ≤ 1+(j-1)*beta := by nlinarith
  exact div_le_self (mul_nonneg (by linarith) hb) hd

lemma regular_increment_bound (b : ℕ) (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (Q : ProbabilityMeasure Message) (hQ : IsPosteriorFixedPoint (PMF.pure b) lam h Q) (hs : SpinSymmetric Q)
    (he : 0 ≤ posteriorEta Q) (j : ℕ) (hj : j < b) :
    3*lam^4*(posteriorMu Q)^2*((j:ℝ)/(1+((j:ℝ)-1)*(lam^2*posteriorMu Q)))-
      lam^4*posteriorMu Q*posteriorNu Q*Real.sqrt j ≤
      3*pairCorrelation lam h Q (degreePosterior lam h Q hQ.1 j) := by
  by_cases hj0 : j=0
  · subst j
    simp only [Nat.cast_zero, zero_div, mul_zero, Real.sqrt_zero, sub_zero]
    exact mul_nonneg (by norm_num) (pairCorrelation_nonneg lam h hl0 hl1 Q _ hQ.1)
  · have hj1 : 1 ≤ j := by omega
    have hjr : (1:ℝ) ≤ j := by exact_mod_cast hj1
    have hm := posteriorMu_nonneg Q
    have hn := posteriorNu_nonneg Q
    let L := (j:ℝ)*(lam^2*posteriorMu Q)/(1+((j:ℝ)-1)*(lam^2*posteriorMu Q))
    have hb : 0 ≤ lam^2*posteriorMu Q := mul_nonneg (sq_nonneg _) hm
    have hL : 0 ≤ L := div_nonneg (mul_nonneg (by positivity) hb) (by positivity)
    have hh := pairCorrelation_truncated lam h hl0 hl1 Q (degreePosterior lam h Q hQ.1 j) hQ.1 hs he
      (partial_nu_le_regular b lam h hl0 hl1 Q hQ (Nat.le_of_lt hj)) hL
      (degree_projection lam h hl0 hl1 Q hQ.1 hs j hj1)
    have hsqrt : Real.sqrt L ≤ lam*Real.sqrt (posteriorMu Q)*Real.sqrt j := by
      have hh := scalar_sqrt_projection_bound hjr hb
      rw [Real.sqrt_mul (show (0:ℝ)≤j by positivity), Real.sqrt_mul (sq_nonneg lam), Real.sqrt_sq_eq_abs, abs_of_nonneg hl0] at hh
      dsimp only [L]
      nlinarith only [hh]
    have hmul := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ lam^3*Real.sqrt (posteriorMu Q)*posteriorNu Q by positivity)
    have hsq := Real.sq_sqrt hm
    have hlead : 3*lam^2*posteriorMu Q*L =
        3*lam^4*(posteriorMu Q)^2*((j:ℝ)/(1+((j:ℝ)-1)*(lam^2*posteriorMu Q))) := by dsimp only [L]; ring
    rw [hlead] at hh
    have hloss : lam^3*Real.sqrt (posteriorMu Q)*posteriorNu Q*(lam*Real.sqrt (posteriorMu Q)*Real.sqrt j) =
        lam^4*posteriorMu Q*posteriorNu Q*Real.sqrt j := by
      calc
        _ = lam^4*(Real.sqrt (posteriorMu Q))^2*posteriorNu Q*Real.sqrt j := by ring
        _ = _ := by rw [hsq]
    rw [hloss] at hmul
    linarith only [hh, hmul]

end ThreeState

namespace ThreeState
open scoped BigOperators

lemma sum_range_real (b : ℕ) : (∑ j ∈ Finset.range b, (j:ℝ)) = (b:ℝ)*(b-1)/2 := by
  induction b with
  | zero => norm_num
  | succ b ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma sum_range_factorial_two (b : ℕ) :
    (∑ j ∈ Finset.range b, (j:ℝ)*((j:ℝ)-1)) = (b:ℝ)*(b-1)*(b-2)/3 := by
  induction b with
  | zero => norm_num
  | succ b ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma reciprocal_tangent {x y D : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hD : 0 < D) :
    x*(2*D-y)/D^2 ≤ x/y := by
  apply (div_le_div_iff₀ (sq_pos_of_pos hD) hy).mpr
  nlinarith only [mul_nonneg hx (sq_nonneg (D-y))]

lemma regular_rational_sum (b : ℕ) (hb : 2 ≤ b) (lam mu : ℝ) (hc : (b:ℝ)*lam^2=1) (hm : 0 ≤ mu) :
    (1-lam^2)/(2*(1+2*mu/3)) ≤
      lam^4*(∑ j ∈ Finset.range b, (j:ℝ)/(1+((j:ℝ)-1)*(lam^2*mu))) := by
  let D := 1+2*mu/3
  have hD : 0 < D := by dsimp [D]; positivity
  have hbr : (2:ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0:ℝ) ≤ b := by positivity
  have hbm : 0 ≤ (b:ℝ)-1 := by linarith
  have hterm (j : ℕ) :
      ((2*D-1)/D^2)*(j:ℝ)-((lam^2*mu)/D^2)*((j:ℝ)*((j:ℝ)-1)) ≤
        (j:ℝ)/(1+((j:ℝ)-1)*(lam^2*mu)) := by
    by_cases hj : j=0
    · subst j; norm_num
    · have hjr : (1:ℝ) ≤ j := by exact_mod_cast (show 1≤j by omega)
      have hd : 0<1+((j:ℝ)-1)*(lam^2*mu) := by positivity
      have hh := reciprocal_tangent (show (0:ℝ)≤j by positivity) hd hD
      convert hh using 1
      ring
  have hs := Finset.sum_le_sum (s := Finset.range b) (fun j _ => hterm j)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_range_real, sum_range_factorial_two] at hs
  have haux : (b:ℝ)*(b-1)/(2*D) ≤
      ((2*D-1)/D^2)*((b:ℝ)*(b-1)/2)-((lam^2*mu)/D^2)*((b:ℝ)*(b-1)*(b-2)/3) := by
    apply (le_sub_iff_add_le).mpr
    field_simp [ne_of_gt hD]
    dsimp only [D]
    have hp : 0 ≤ mu*((b:ℝ)-1)*lam^2 := by positivity
    nlinarith only [hp, congrArg (fun x => mu*((b:ℝ)-1)*x) hc]
  have hh := mul_le_mul_of_nonneg_left (haux.trans hs) (show (0:ℝ) ≤ lam^4 by positivity)
  have he : lam^4*((b:ℝ)*(b-1)/(2*D)) = (1-lam^2)/(2*D) := by
    have ht : lam^4*((b:ℝ)*(b-1)) = 1-lam^2 := by
      calc
        _ = ((b:ℝ)*lam^2)*(((b:ℝ)*lam^2)-lam^2) := by ring
        _ = _ := by rw [hc]; ring
    calc
      _ = (lam^4*((b:ℝ)*(b-1)))/(2*D) := by ring
      _ = _ := by rw [ht]
  change lam^4*((b:ℝ)*(b-1)/(2*D)) ≤ lam^4*(∑ j ∈ Finset.range b, (j:ℝ)/(1+((j:ℝ)-1)*(lam^2*mu))) at hh
  rwa [he] at hh

lemma regular_sqrt_sum_sq (b : ℕ) (hb : 1 ≤ b) :
    (∑ j ∈ Finset.range b, Real.sqrt (j:ℝ))^2 ≤ (b:ℝ)*(b-1)^2/2 := by
  let f : ℕ → ℝ := fun j => if j=0 then 0 else 1
  let g : ℕ → ℝ := fun j => Real.sqrt (j:ℝ)
  have hf : (∑ j ∈ Finset.range b, (f j)^2) = (b:ℝ)-1 := by
    have hzero : 0 ∈ Finset.range b := Finset.mem_range.mpr (by omega)
    have he (j : ℕ) : (f j)^2 = 1-(if j=0 then (1:ℝ) else 0) := by dsimp only [f]; split_ifs <;> norm_num
    simp only [he, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Finset.sum_ite_eq', hzero, ite_true, mul_one]
  have hg : (∑ j ∈ Finset.range b, (g j)^2) = (b:ℝ)*(b-1)/2 := by
    simp only [g, Real.sq_sqrt (Nat.cast_nonneg _), sum_range_real]
  have hfg : (∑ j ∈ Finset.range b, f j*g j) = ∑ j ∈ Finset.range b, Real.sqrt (j:ℝ) := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j=0 <;> simp [f,g,hj]
  have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range b) f g
  rw [hf,hg,hfg] at hh
  nlinarith only [hh]

lemma regular_sqrt_sum (b : ℕ) (hb : 2 ≤ b) (lam : ℝ) (hl : 0 ≤ lam) (hc : (b:ℝ)*lam^2=1) :
    lam^4*(∑ j ∈ Finset.range b, Real.sqrt (j:ℝ)) ≤ (1-lam^2)*lam/Real.sqrt 2 := by
  have hbr : (2:ℝ) ≤ b := by exact_mod_cast hb
  have ha : 0 ≤ 1-lam^2 := by nlinarith [sq_nonneg lam]
  have hs := regular_sqrt_sum_sq b (by omega)
  have hp := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2*lam^8 by positivity)
  have he : 2*lam^8*((b:ℝ)*(b-1)^2/2) = ((1-lam^2)*lam)^2 := by
    calc
      _ = lam^2*((b:ℝ)*lam^2)*(((b:ℝ)*lam^2)-lam^2)^2 := by ring
      _ = _ := by rw [hc]; ring
  rw [he] at hp
  have hs0 : 0 ≤ ∑ j ∈ Finset.range b, Real.sqrt (j:ℝ) := Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _)
  have hr : 0 < Real.sqrt 2 := by positivity
  apply (le_div_iff₀ hr).mpr
  have hroot : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hx : 0 ≤ lam^4*(∑ j ∈ Finset.range b, Real.sqrt (j:ℝ))*Real.sqrt 2 := by positivity
  have hy : 0 ≤ (1-lam^2)*lam := mul_nonneg ha hl
  apply (sq_le_sq₀ hx hy).mp
  have hsq : (lam^4*(∑ j ∈ Finset.range b, Real.sqrt (j:ℝ))*Real.sqrt 2)^2 =
      2*lam^8*(∑ j ∈ Finset.range b, Real.sqrt (j:ℝ))^2 := by
    calc
      _ = lam^8*(∑ j ∈ Finset.range b, Real.sqrt (j:ℝ))^2*(Real.sqrt 2)^2 := by ring
      _ = _ := by rw [hroot]; ring
  rwa [hsq]

end ThreeState

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

lemma regular_correlation_bound (b : ℕ) (hb : 2 ≤ b) (lam : ℝ) (h : Admissible lam)
    (hl0 : 0 ≤ lam) (hl1 : lam < 1) (hc : (b:ℝ)*lam^2=1)
    (Q : ProbabilityMeasure Message) (hQ : IsPosteriorFixedPoint (PMF.pure b) lam h Q)
    (hs : SpinSymmetric Q) (he : 0 ≤ posteriorEta Q) :
    (1-lam^2)*(3*(posteriorMu Q)^2/(2*(1+2*posteriorMu Q/3))-
      lam*posteriorMu Q*posteriorNu Q/Real.sqrt 2) ≤ 3*correlationEntropy lam h Q b := by
  have hm := posteriorMu_nonneg Q
  have hn := posteriorNu_nonneg Q
  have hsum := Finset.sum_le_sum (s := Finset.range b) (fun j hj =>
    regular_increment_bound b lam h hl0 hl1 Q hQ hs he j (Finset.mem_range.mp hj))
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    ← correlationEntropy_sum lam h hl0 hl1 Q hQ.1 b] at hsum
  have hpos := mul_le_mul_of_nonneg_left (regular_rational_sum b hb lam (posteriorMu Q) hc hm)
    (show 0 ≤ 3*(posteriorMu Q)^2 by positivity)
  have hneg := mul_le_mul_of_nonneg_left (regular_sqrt_sum b hb lam hl0 hc)
    (mul_nonneg hm hn)
  calc
    _ = 3*(posteriorMu Q)^2*((1-lam^2)/(2*(1+2*posteriorMu Q/3)))-
        (posteriorMu Q*posteriorNu Q)*((1-lam^2)*lam/Real.sqrt 2) := by ring
    _ ≤ 3*(posteriorMu Q)^2*(lam^4*(∑ j ∈ Finset.range b, (j:ℝ)/(1+((j:ℝ)-1)*(lam^2*posteriorMu Q))))-
        (posteriorMu Q*posteriorNu Q)*(lam^4*(∑ j ∈ Finset.range b, Real.sqrt (j:ℝ))) := sub_le_sub hpos hneg
    _ = _ := by ring
    _ ≤ _ := hsum

lemma entropyF_sourceF (m : Message) : entropyF m = Radial.sourceF (fun i => m i) := by
  simp only [entropyF, entropyI, entropyJ, entropyB, Radial.sourceF, mLog, mCenteredLog,
    Radial.avg_expand]
  ring

lemma continuous_entropyF_edge (lam : ℝ) (h : Admissible lam) (hl0 : 0 ≤ lam) (hl1 : lam < 1) :
    Continuous (fun m => entropyF (edgeMessage lam h m)) :=
  (((continuous_entropyI_edge lam h hl0 hl1).const_mul 3).sub
    ((continuous_entropyJ_edge lam h hl0 hl1).const_mul 2)).add
      ((continuous_entropyB_edge lam h hl0 hl1).const_mul (4/5:ℝ))

lemma integral_entropyF_radial (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (hl0 : 0 < lam) (hl1 : lam < 1) (Q : ProbabilityMeasure Message)
    (hQ : IsPosteriorFixedPoint offspring lam h Q)
    (hD2 : HasMean offspring (fun n : ℕ => (n:ℝ)^2)) :
    (1-lam^2)/2*posteriorNu Q ≤ (∫ m, entropyF m ∂(Q : Measure Message))-
      lam⁻¹^2*(∫ m, entropyF (edgeMessage lam h m) ∂(Q : Measure Message)) := by
  have hi := integrable_entropyF_fixedpoint offspring lam h hl0.le hl1 Q hQ hD2
  have hie := integrable_continuous_message Q (continuous_entropyF_edge lam h hl0.le hl1)
  have hp := positive_fixedpoint offspring lam h hl0.le hl1 Q hQ
  have hh := integral_mono_ae ((integrable_continuous_message Q (continuous_messageX.pow 2)).const_mul ((1-lam^2)/2))
    (show Integrable (fun m => entropyF m-lam⁻¹^2*entropyF (edgeMessage lam h m)) (Q : Measure Message) from hi.sub (hie.const_mul _))
    (hp.mono (fun m hm => by
      have hh := Radial.radial_source (fun i => m i) (average_message m) hm lam hl0 hl1
      change (1-lam^2)/2*(messageX m)^2 ≤ entropyF m-lam⁻¹^2*entropyF (edgeMessage lam h m)
      rw [entropyF_sourceF, entropyF_sourceF]
      convert hh using 1 <;> simp only [edgeMessage, messageX, messageDeviation, Radial.momentX]
      ring))
  rw [integral_const_mul, integral_sub hi (hie.const_mul _), integral_const_mul] at hh
  exact hh

lemma regular_entropy_bound (b : ℕ) (hb : 2 ≤ b) (lam : ℝ) (h : Admissible lam)
    (hl0 : 0 < lam) (hl1 : lam < 1) (hc : (b:ℝ)*lam^2=1)
    (Q : ProbabilityMeasure Message) (hQ : IsPosteriorFixedPoint (PMF.pure b) lam h Q)
    (hs : SpinSymmetric Q) (he : 0 ≤ posteriorEta Q) :
    posteriorNu Q/2+3*(posteriorMu Q)^2/(2*(1+2*posteriorMu Q/3))-
      lam*posteriorMu Q*posteriorNu Q/Real.sqrt 2 ≤
        (8/5:ℝ)*(∫ m, entropyJ m ∂(Q : Measure Message))^2 := by
  have hD2 : HasMean (PMF.pure b) (fun n : ℕ => (n:ℝ)^2) := hasMean_pure _ _
  have hD := hasMean_of_square hD2
  have hid := entropy_identity (PMF.pure b) lam h hl0.le hl1 Q hQ hs hD2
  have hrad := integral_entropyF_radial (PMF.pure b) lam h hl0 hl1 Q hQ hD2
  have hcorr := regular_correlation_bound b hb lam h hl0.le hl1 hc Q hQ hs he
  have hJ := additive_entropyJ (PMF.pure b) lam h hl0.le hl1 Q hQ hs hD
  simp only [mean_pure] at hid hJ
  have hl : lam⁻¹^2 = (b:ℝ) := by field_simp; nlinarith only [hc]
  rw [hl] at hrad
  have hJe : (∫ m, entropyJ (edgeMessage lam h m) ∂(Q : Measure Message)) =
      lam^2*(∫ m, entropyJ m ∂(Q : Measure Message)) := by
    nlinarith only [hJ, congrArg (fun x : ℝ => x*(∫ m, entropyJ (edgeMessage lam h m) ∂(Q : Measure Message))) hc]
  rw [hJe] at hid
  have hfac : (b:ℝ)*(b-1)*lam^4=1-lam^2 := by
    calc
      _ = ((b:ℝ)*lam^2)*(((b:ℝ)*lam^2)-lam^2) := by ring
      _ = _ := by rw [hc]; ring
  have hid' : (1-lam^2)/2*posteriorNu Q+3*correlationEntropy lam h Q b ≤
      (8/5:ℝ)*(1-lam^2)*(∫ m, entropyJ m ∂(Q : Measure Message))^2 := by
    nlinarith only [hid, hrad, congrArg (fun x : ℝ => (8/5:ℝ)*x*(∫ m, entropyJ m ∂(Q : Measure Message))^2) hfac]
  have ha : 0 < 1-lam^2 := by nlinarith
  apply (mul_le_mul_iff_left₀ ha).mp
  nlinarith only [hid', hcorr]

end ThreeState

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

lemma critical_moment_nu_bound (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (hl0 : 0 < lam) (hl1 : lam < 1) (Q : ProbabilityMeasure Message)
    (hQ : IsPosteriorFixedPoint offspring lam h Q) (hs : SpinSymmetric Q)
    (hD : HasMean offspring (fun n : ℕ => (n:ℝ)))
    (hc : mean offspring (fun n : ℕ => (n:ℝ))*lam^2=1) :
    ((37/27:ℝ)+2*lam*((37/27:ℝ)/(2+lam)))^2*posteriorNu Q ≤ posteriorMu Q := by
  have hh := positive_moment_estimates offspring lam h hl0 hl1 Q hQ hs hD hc
  dsimp only at hh
  have hnu := posteriorNu_nonneg Q
  have hmu := posteriorMu_nonneg Q
  by_cases hzero : posteriorNu Q=0
  · simp only [hzero,mul_zero]
    exact hmu
  · have hnupos : 0 < posteriorNu Q := lt_of_le_of_ne hnu (Ne.symm hzero)
    have he : 0 ≤ ((37/27:ℝ)+2*lam*((37/27:ℝ)/(2+lam)))*posteriorNu Q := by positivity
    have hsq := (Real.le_sqrt he (mul_nonneg hmu hnu)).mp (hh.2.2.1.trans hh.2.2.2)
    apply (mul_le_mul_iff_left₀ hnupos).mp
    nlinarith only [hsq]

lemma regular_positive_critical_uniform (b : ℕ) (hb : 2 ≤ b) (lam : ℝ) (h : Admissible lam)
    (hl0 : 0 < lam) (hc : (b:ℝ)*lam^2=1)
    (Q : ProbabilityMeasure Message) (hQ : IsPosteriorFixedPoint (PMF.pure b) lam h Q)
    (hs : SpinSymmetric Q) : posteriorMu Q = 0 := by
  have hbr : (2:ℝ) ≤ b := by exact_mod_cast hb
  have hlhalf : lam^2 ≤ 1/2 := by nlinarith [sq_nonneg lam]
  have hl1 : lam < 1 := by nlinarith
  have hD : HasMean (PMF.pure b) (fun n : ℕ => (n:ℝ)) := hasMean_pure _ _
  have hc' : mean (PMF.pure b) (fun n : ℕ => (n:ℝ))*lam^2=1 := by simpa only [mean_pure] using hc
  have hh := positive_moment_estimates (PMF.pure b) lam h hl0 hl1 Q hQ hs hD hc'
  dsimp only at hh
  have hm := posteriorMu_nonneg Q
  have hn := posteriorNu_nonneg Q
  have he : 0 ≤ posteriorEta Q := (show 0 ≤ ((37/27:ℝ)+2*lam*((37/27:ℝ)/(2+lam)))*posteriorNu Q by positivity).trans hh.2.2.1
  have hent := regular_entropy_bound b hb lam h hl0 hl1 hc Q hQ hs he
  have hcnu := critical_moment_nu_bound (PMF.pure b) lam h hl0 hl1 Q hQ hs hD hc'
  by_contra hzero
  have hmpos : 0 < posteriorMu Q := lt_of_le_of_ne hm (Ne.symm hzero)
  apply PositiveScalar.moment_scalar_contradiction lam (posteriorMu Q) (posteriorNu Q)
    (∫ m, entropyJ m ∂(Q : Measure Message)) 1 hl0 hl1 hmpos hn (by norm_num) (by norm_num)
    (by simpa only [one_mul] using posteriorMu_sq_le Q) hcnu hh.1 hh.2.1
  · nlinarith only [hent, mul_nonneg (sq_nonneg lam) hn]
  · intro hhigher
    linarith only [hhigher,hlhalf]

lemma messageX_zero_tv {m : Message} (hm : messageX m=0) : messageTV m=0 := by
  have hc : ∀ i : Spin, m i=1 := by
    have h0 := sq_nonneg (m 0-1)
    have h1 := sq_nonneg (m 1-1)
    have h2 := sq_nonneg (m 2-1)
    simp only [messageX, Radial.momentX, Radial.avg_expand, messageDeviation] at hm
    intro i
    fin_cases i <;> (try change m 0=1) <;> (try change m 1=1) <;> (try change m 2=1) <;> nlinarith
  simp [messageTV,hc]

lemma integral_tv_zero_of_mu_zero (Q : ProbabilityMeasure Message) (hmu : posteriorMu Q=0) :
    ∫ m, messageTV m ∂(Q : Measure Message) = 0 := by
  have ha := (integral_eq_zero_iff_of_nonneg messageX_nonneg (integrable_continuous_message Q continuous_messageX)).mp hmu
  calc
    _ = ∫ _m : Message, (0:ℝ) ∂(Q : Measure Message) := integral_congr_ae (ha.mono (fun m hm => messageX_zero_tv hm))
    _ = 0 := integral_zero _ _

lemma observed_tendsto_zero_of_uniform_fixedpoints (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (hunif : ∀ Q : ProbabilityMeasure Message, IsPosteriorFixedPoint offspring lam h Q → SpinSymmetric Q → posteriorMu Q=0) :
    Tendsto (fun n => advantage (observedLaw offspring lam h n)) atTop (𝓝 0) := by
  obtain ⟨Q,hQ,hs,φ,hφ,hlim⟩ := ordered_exists_symmetric_fixedpoint offspring lam h
  have htv := integral_tv_zero_of_mu_zero Q (hunif Q hQ hs)
  have hordered := advantage_tendsto_of_likelihood (fun n => orderedLaw offspring lam h (φ n)) hlim
  rw [htv] at hordered
  obtain ⟨L,hL,_hL1,hactual⟩ := observedAdvantage_tendsto offspring lam h
  have hle := le_of_tendsto_of_tendsto (hactual.comp hφ.tendsto_atTop) hordered
    (Eventually.of_forall (fun n => orderedAdvantage_dominates offspring lam h (φ n)))
  have heq : L=0 := le_antisymm hle hL
  simpa only [heq] using hactual

 
theorem regular_positive_critical_nonreconstruction (b : ℕ) (hb : 2 ≤ b) (lam : ℝ)
    (h : Admissible lam) (hl0 : 0 < lam) (hc : (b:ℝ)*lam^2=1) :
    Tendsto (regularAdvantage b lam h) atTop (𝓝 0) := by
  exact observed_tendsto_zero_of_uniform_fixedpoints (PMF.pure b) lam h
    (regular_positive_critical_uniform b hb lam h hl0 hc)

end ThreeState

end OAI
