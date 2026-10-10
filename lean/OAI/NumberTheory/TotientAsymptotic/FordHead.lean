import OAI.NumberTheory.TotientAsymptotic.UntruncatedRemainder
import OAI.NumberTheory.TotientAsymptotic.PreimageOmega

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma first_band_small : ∀ᶠ x : ℝ in atTop,
    (11/10 : ℝ)*bandScale x 1 ≤ (7/10 : ℝ)*B x := by
  filter_upwards [B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    m_tendsto.eventually (eventually_gt_atTop 0),
    bandCenterRatio_tendsto.eventually (eventually_gt_nhds (by norm_num : (9/10 : ℝ)<1))]
    with x hB hm hr
  have he := fordBandScale_eq_ratio_mul (i := 0) hB hm
  have he0 : fordBandScale x 0=B x := by simp [fordBandScale]
  rw [he0] at he
  have hb0 : bandScale x 0 ≤ (10/9 : ℝ)*B x := by nlinarith [bandScale_nonnegative x 0]
  have hb := bandScale_succ_le x 0
  have hρ := collision_rho_bounds.2
  have hp := bandScale_nonnegative x 0
  have hh : bandScale x 1 ≤ (137/250 : ℝ)*((10/9 : ℝ)*B x) :=
    hb.trans (mul_le_mul hρ.le hb0 hp (by norm_num))
  nlinarith

lemma ford_rest_le_power {n : ℕ} (hlen : 1 < n.primeFactorsList.length) :
    fordCofactor n 1 ≤ (fordPrime n 1)^n.primeFactorsList.length := by
  let l := n.primeFactorsList.reverse.drop 1
  have hh : l.prod ≤ (fordPrime n 1)^l.length := by
    apply List.prod_le_pow_length
    intro q hq
    obtain ⟨j,hj,he⟩ := List.mem_drop_iff_getElem.mp hq
    have hj' : 1+j < n.primeFactorsList.length := by simpa only [List.length_reverse,Nat.add_comm] using hj
    rw [← he,← fordPrime_eq_get hj']
    exact fordPrime_antitone hlen hj' (by omega)
  exact hh.trans (Nat.pow_le_pow_right (fordPrime_prime hlen).pos (by
    dsimp [l]
    simp))

lemma ford_log_factorization {n : ℕ} (hn : 0 < n) (hlen : 1 < n.primeFactorsList.length) :
    Real.log n ≤ Real.log (fordPrime n 0)+
      n.primeFactorsList.length*Real.log (fordPrime n 1) := by
  have hp0 := fordPrime_prime (show 0<n.primeFactorsList.length by omega)
  have htail := fordCofactor_pos n 1
  have he : n=fordPrime n 0*fordCofactor n 1 := by
    simpa only [Finset.range_one,Finset.prod_singleton,mul_comm] using
      ford_factorization hn (show 1≤n.primeFactorsList.length by omega)
  have hlog := Real.log_le_log (show (0 : ℝ)<fordCofactor n 1 by exact_mod_cast htail)
    (show (fordCofactor n 1 : ℝ) ≤ (fordPrime n 1 : ℝ)^n.primeFactorsList.length by exact_mod_cast ford_rest_le_power hlen)
  rw [Real.log_pow] at hlog
  have heR : Real.log n=Real.log (fordPrime n 0)+Real.log (fordCofactor n 1) := by
    conv_lhs => rw [he]
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp0.ne_zero) (by exact_mod_cast htail.ne')]
  linarith

lemma head_remainder_log_error : ∀ᶠ b : ℝ in atTop,
    21*b*Real.exp ((7/10 : ℝ)*b) ≤ (1/20 : ℝ)*Real.exp b := by
  have ht : Tendsto (fun b : ℝ => 21*b*Real.exp (-(3/10 : ℝ)*b)) atTop (nhds 0) := by
    simpa only [Real.rpow_one,mul_assoc,mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (3/10) (by norm_num : (0 : ℝ)<3/10)).const_mul 21
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/20))] with b hb
  have hh := mul_le_mul_of_nonneg_right hb.le (Real.exp_pos b).le
  rw [mul_assoc,← Real.exp_add] at hh
  simpa only [show -(3/10 : ℝ)*b+b=(7/10 : ℝ)*b by ring] using hh

/-- All preimages outside the small-value and high-Omega sets have a head
prime in the required range. The constants leave room for the coarse bands. -/
theorem extracted_head_large : ∀ᶠ x : ℝ in atTop, ∀ H n : ℕ,
    0 < L x H → 0 < n → extractedStructureCondition x (P H) n →
    x^(19/20 : ℝ) ≤ n.totient → (n.totient.primeFactorsList.length : ℝ) ≤ 20*B x →
    x^(9/10 : ℝ) ≤ fordPrime n 0 := by
  filter_upwards [first_band_small,B_tendsto.eventually head_remainder_log_error,
    B_tendsto.eventually (eventually_ge_atTop (1 : ℝ)),eventually_gt_atTop (1 : ℝ)]
    with x hb he hB hx
  intro H n hL hn hs hval hΩ
  have hlast := fordPrime_index_of_doubleLog_pos (lt_trans (by norm_num) hs.2.1)
  have hlen : 1<n.primeFactorsList.length := lt_of_le_of_lt hL hlast
  have hprime := fordPrime_prime hlen
  have hp0 := fordPrime_prime (show 0<n.primeFactorsList.length by omega)
  have hpn : (0 : ℝ)<fordPrime n 1 := by exact_mod_cast hprime.pos
  have hlogpn : 0 < Real.log (fordPrime n 1 : ℝ) := Real.log_pos (by exact_mod_cast hprime.one_lt)
  have hb1 : primeDoubleLog n 1 ≤ (7/10 : ℝ)*B x :=
    ((hs.1 1 (Finset.mem_Icc.mpr ⟨le_rfl,hL⟩)).2).trans hb
  have hp1 : Real.log (fordPrime n 1 : ℝ) ≤ Real.exp ((7/10 : ℝ)*B x) :=
    (Real.log_le_iff_le_exp hlogpn).mp hb1
  have hΩn : (n.primeFactorsList.length : ℝ) ≤ 21*B x := by
    have hh : (n.primeFactorsList.length : ℝ) ≤ n.totient.primeFactorsList.length+1 :=
      by exact_mod_cast preimage_factor_count hn
    linarith
  have hbound := ford_log_factorization hn hlen
  have hrest := mul_le_mul hΩn hp1 hlogpn.le (by positivity : (0 : ℝ) ≤ 21*B x)
  have hexp : Real.exp (B x)=Real.log x := Real.exp_log (Real.log_pos hx)
  rw [hexp] at he
  have hvn : x^(19/20 : ℝ) ≤ (n : ℝ) := hval.trans (by exact_mod_cast Nat.totient_le n)
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hvlog := Real.log_le_log (Real.rpow_pos_of_pos (zero_lt_one.trans hx) _) hvn
  rw [Real.log_rpow (zero_lt_one.trans hx)] at hvlog
  have hh : (9/10 : ℝ)*Real.log x ≤ Real.log (fordPrime n 0) := by linarith
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hx)]
  apply (Real.le_log_iff_exp_le (by exact_mod_cast hp0.pos)).mp
  simpa only [mul_comm] using hh

end TotientAsymptotic

end

end OAI
