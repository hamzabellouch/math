import OAI.NumberTheory.TotientAsymptotic.PrefixPreimage
import OAI.NumberTheory.TotientAsymptotic.TailBelowPrefix

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma remainderTail_dvd_suffix {x : ℝ} {H : ℕ} (η : RemainderDatum (L x H))
    (hRL : R x H ≤ L x H) : remainderTail x H η ∣ suffixPreimage η 0 := by
  have he : suffixPreimage η 0 = remainderTail x H η *
      ∏ i ∈ Finset.Icc 1 (R x H), remainderPrime η i := by
    unfold suffixPreimage remainderTail
    rw [prod_Icc_split_at (Nat.zero_le (R x H)) hRL]
    simp only [Nat.zero_add]
    ring
  rw [he]
  exact dvd_mul_right _ _

lemma basic_tail_lt_all_tuple_primes : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ p : ℕ, p.Prime → x^(9/10 : ℝ) ≤ p →
    ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η →
    ∀ i, remainderTail x H η < tuplePrimes (witnessTuple p η) i := by
  filter_upwards [basic_tail_lt_last_prefix,eventually_ge_atTop 2,
    P_tendsto.eventually (eventually_ge_atTop 1)] with H hlast hH hP
  filter_upwards [theta_eventually_mem,m_tendsto.eventually (eventually_gt_atTop H),
    basic_remainder_subpower H (show (0 : ℝ)<1/10 by norm_num),
    eventually_gt_atTop (1 : ℝ)] with x hs hm hsub hx1
  intro p hp hpl η hη i
  have hPH := P_lt_self hH
  have hRL : R x H < L x H := by unfold R L; omega
  have hLm : L x H < m x := by unfold L; omega
  have hRpos : 0 < R x H := by unfold R; omega
  refine Fin.cases ?_ (fun j => ?_) i
  · change remainderTail x H η < p
    have hwle : remainderTail x H η ≤ suffixPreimage η 0 :=
      Nat.le_of_dvd (suffixPreimage_pos hη) (remainderTail_dvd_suffix η hRL.le)
    have hsmall := (show (remainderTail x H η : ℝ) ≤ suffixPreimage η 0 by exact_mod_cast hwle).trans (hsub η hη)
    exact_mod_cast hsmall.trans_lt ((Real.rpow_lt_rpow_of_exponent_lt hx1
      (show (1/10 : ℝ)<9/10 by norm_num)).trans_le hpl)
  · change remainderTail x H η < remainderPrime η (j.val+1)
    have hj : j.val+1 ≤ R x H := by have := j.isLt; omega
    have hl := hlast x hs hm η hη
    rcases lt_or_eq_of_le hj with hj | hj
    · exact hl.trans (basic_remainder_prime_strictAnti hη
        (Finset.mem_Icc.mpr ⟨by omega,hj.le.trans hRL.le⟩)
        (Finset.mem_Icc.mpr ⟨hRpos,hRL.le⟩) hj (hj.trans hRL |>.trans hLm))
    · simpa only [hj] using hl

/-- Every basic tuple has the candidate obtained by replacing its arithmetic
tail by the least inverse image of the same tail totient. -/
theorem basic_tuple_candidate_realizes : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ t : ℝ, ∀ τ : TotientTuple (R x H), IsBasicTuple x H t τ →
      (tupleLeastCandidate τ).totient=tupleValue τ := by
  filter_upwards [basic_tail_lt_all_tuple_primes,eventually_tail_cut_separated]
    with H hsmall hH
  obtain ⟨hP,hcuts⟩ := hH
  have hPH : P H < H := by omega
  filter_upwards [hsmall,basic_head_coprime H,m_tendsto.eventually (eventually_ge_atTop H)]
    with x hsmall hc hm
  intro t τ hτ
  obtain ⟨η,hη,he⟩ := (isPrefixDatum_iff x H τ.tail).mp hτ.2.2.1
  have hτe : witnessTuple τ.head η=τ := by
    cases τ
    simpa only [witnessTuple,TotientTuple.mk.injEq,true_and] using he
  have hRL : R x H < L x H := by unfold R L; omega
  apply tuple_candidate_realizes (w := remainderTail x H η) hPH.le hτ (suffixPreimage_pos (i := R x H) hη)
  · exact congrArg PrefixDatum.d he
  · intro i
    rw [← hτe]
    exact hsmall _ hτ.1 hτ.2.1 η hη i
  · rw [← hτe,← wholePreimage_prefix_split _ _ hRL.le]
    exact wholePreimage_totient hτ.1 hη (by unfold L; omega) hRL
      (hc _ hτ.1 hτ.2.1 η hη)

end TotientAsymptotic

end

end OAI
