import OAI.Combinatorics.KMedianRecovery.Refined.Model
import OAI.Combinatorics.KMedianRecovery.Encoding.Reencode
import OAI.Combinatorics.KMedian.Binary.BooleanPolynomial

namespace OAI

namespace MetricKMedianRecovery.RefinedRecovery

private lemma bits_length_le (n : ℕ) : n.bits.length ≤ n + 1 := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr ((show n < 2^n from Nat.lt_two_pow_self).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega)))

private lemma natBits_length_le (n : ℕ) :
    (RationalMetricInput.natBits n).length ≤ 2*n+3 := by
  simp only [RationalMetricInput.natBits, List.length_append, List.length_replicate,
    List.length_singleton]
  have := bits_length_le n
  omega

private lemma rationalBits_nat_length (n : ℕ) :
    (RationalMetricInput.rationalBits (n : ℚ)).length ≤ 2*n+7 := by
  simp only [RationalMetricInput.rationalBits, List.length_append, List.length_singleton,
    Rat.num_natCast, Int.natAbs_natCast, Rat.den_natCast]
  have := natBits_length_le n
  norm_num [RationalMetricInput.natBits, Nat.bits] at *
  omega

noncomputable def metricLengthPolynomial (b : Polynomial ℕ) : Polynomial ℕ :=
  6*(Polynomial.X+1) + Polynomial.X^2*(2*b+7)

lemma metric_length_bound (I : Input) (b : Polynomial ℕ) (h : I.Bounded b) :
    I.metric.bits.length ≤ (metricLengthPolynomial b).eval I.size := by
  have hn : I.metric.pointCount ≤ I.size := by
    calc
      _ = (I.metric.clients ∪ I.metric.facilities).card := by rw [I.metric.covered]; simp
      _ ≤ I.size := Finset.card_union_le _ _
  have hk : I.metric.budget ≤ I.size :=
    I.anchor_card.symm.trans_le ((Finset.card_le_card I.anchor_subset).trans
      (by unfold Input.size RationalMetricInput.size; omega))
  have he (i j : I.Point) :
      (RationalMetricInput.rationalBits (I.metric.distance i j)).length ≤ 2*b.eval I.size+7 := by
    obtain ⟨z, hz⟩ := I.integral i j
    rw [hz]
    have hzb : z ≤ b.eval I.size := by exact_mod_cast (hz ▸ h i j)
    exact (rationalBits_nat_length z).trans (by omega)
  have hr (i : I.Point) :
      ((List.ofFn (fun j : I.Point => RationalMetricInput.rationalBits
        (I.metric.distance i j))).flatten).length ≤ I.metric.pointCount*(2*b.eval I.size+7) := by
    simp only [List.length_flatten, List.map_ofFn, List.sum_ofFn]
    exact (Finset.sum_le_sum (fun j _ => he i j)).trans_eq (by simp)
  have hm : ((List.ofFn (fun i : I.Point =>
      (List.ofFn (fun j : I.Point => RationalMetricInput.rationalBits
        (I.metric.distance i j))).flatten)).flatten).length ≤
      I.metric.pointCount^2*(2*b.eval I.size+7) := by
    simp only [List.length_flatten, List.map_ofFn, List.sum_ofFn]
    apply (Finset.sum_le_sum (fun i _ => hr i)).trans_eq
    simp [pow_two, mul_assoc]
  have hp := natBits_length_le I.metric.pointCount
  have hb := natBits_length_le I.metric.budget
  dsimp only [Input.Point] at hm
  have hpow : I.metric.pointCount^2*(2*b.eval I.size+7) ≤ I.size^2*(2*b.eval I.size+7) := by
    gcongr
  simp only [RationalMetricInput.bits, List.length_append, List.length_ofFn]
  simp only [metricLengthPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
  omega

private lemma polynomial_power_bound (p : Polynomial ℕ) :
    ∃ c d : ℕ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → p.eval n ≤ c*n^d := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, d, ha, hp⟩ := hp
    obtain ⟨b, e, hb, hq⟩ := hq
    refine ⟨a+b, d+e, by omega, fun n hn => ?_⟩
    rw [Polynomial.eval_add, add_mul]
    apply Nat.add_le_add
    · exact (hp n hn).trans (Nat.mul_le_mul_left a (Nat.pow_le_pow_right hn (by omega)))
    · exact (hq n hn).trans (Nat.mul_le_mul_left b (Nat.pow_le_pow_right hn (by omega)))
  | monomial d a =>
    refine ⟨a+1, d, by omega, fun n _ => ?_⟩
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_right _ (by omega)

lemma zero_random_polynomialWork (A : BinaryRandomizedAlgorithm)
    (hA : A.randomBits = 0) (b : Polynomial ℕ) : PolynomialWork A b := by
  let p := metricLengthPolynomial b
  let q := 2*p + 2*Polynomial.X + 2
  let w := Polynomial.X + A.computation.time.comp (2*Polynomial.X+1)
  obtain ⟨c, d, hc, hpow⟩ := polynomial_power_bound (w.comp q)
  let K : ℝ := 3 + 1/Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨c*K^d, by positivity, d, ?_⟩
  intro I hI ζ hζ hζ1
  let t := I.size + precision ζ + 1
  have hseed : seedLength A I ζ = 0 := by simp [seedLength, hA]
  have hlen : (queryBits I ζ).length ≤ q.eval t := by
    have hM := (metric_length_bound I b hI).trans
      (MetricKMedian.Binary.polynomial_eval_mono p (show I.size ≤ t by dsimp [t]; omega))
    have hn : I.metric.pointCount ≤ I.size := by
      calc
        _ = (I.metric.clients ∪ I.metric.facilities).card := by rw [I.metric.covered]; simp
        _ ≤ I.size := Finset.card_union_le _ _
    simp only [queryBits, BitMachine.pairBits_length, Input.anchorBits,
      List.length_append, List.length_ofFn, List.length_replicate]
    simp only [q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X]
    omega
  have hw : workBound A I ζ ≤ c*t^d := by
    have hb : workBound A I ζ = w.eval (queryBits I ζ).length := by
      simp [workBound, hseed, w, BitMachine.pairBits_length]
    rw [hb]
    exact (MetricKMedian.Binary.polynomial_eval_mono w hlen).trans
      (by simpa only [Polynomial.eval_comp] using hpow t (by dsimp [t]; omega))
  have hlog : 0 ≤ Real.log (1/ζ) := Real.log_nonneg (by
    rw [le_div_iff₀ hζ]
    linarith)
  have hprec : (precision ζ : ℝ) ≤ Real.log (1/ζ)/Real.log 2 + 1 := by
    exact (Nat.ceil_lt_add_one (div_nonneg hlog hlog2.le)).le
  have ht : (t : ℝ) ≤ K*((I.size : ℝ)+1)*(1+Real.log (1/ζ)) := by
    have hN : (0 : ℝ) ≤ I.size := Nat.cast_nonneg _
    have hi : 0 ≤ 1/Real.log 2 := by positivity
    have hprec' : (precision ζ : ℝ)+1 ≤ K*(1+Real.log (1/ζ)) := by
      change (precision ζ : ℝ) ≤ Real.log (1/ζ)*(Real.log 2)⁻¹+1 at hprec
      rw [one_div] at hi
      dsimp only [K]
      rw [one_div]
      nlinarith [mul_nonneg hi hlog]
    calc
      (t : ℝ) ≤ ((I.size : ℝ)+1)*((precision ζ : ℝ)+1) := by
        dsimp [t]
        push_cast
        nlinarith [mul_nonneg hN (Nat.cast_nonneg (α := ℝ) (precision ζ))]
      _ ≤ ((I.size : ℝ)+1)*(K*(1+Real.log (1/ζ))) := by gcongr
      _ = _ := by ring
  have hwR : (workBound A I ζ : ℝ) ≤ (c : ℝ)*(t : ℝ)^d := by exact_mod_cast hw
  apply hwR.trans
  calc
    _ ≤ (c : ℝ)*(K*((I.size : ℝ)+1)*(1+Real.log (1/ζ)))^d := by gcongr
    _ = _ := by simp only [mul_pow]; ring

end MetricKMedianRecovery.RefinedRecovery

end OAI
