import OAI.NumberTheory.TotientAsymptotic.PrefixWeight

namespace OAI

noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

def tupleQ {r : ℕ} (τ : TotientTuple r) : ℝ :=
  prefixQ τ.tail*(1-(1 : ℝ)/τ.head)

lemma tuple_least_ratio_identity {x : ℝ} {H : ℕ} (hPH : P H ≤ H)
    {τ : TotientTuple (R x H)} (hτ : IsBasicTuple x H x τ)
    (hell : ell (tupleValue τ)=tupleLeastCandidate τ) :
    ((ell (tupleValue τ) : ℝ)/tupleValue τ)*tupleQ τ=(ell τ.tail.d : ℝ)/τ.tail.d := by
  have hp := hτ.1
  have hp1 : (1 : ℝ)<τ.head := by exact_mod_cast hp.one_lt
  have hD : (0 : ℝ)<prefixDenominator τ.tail := by
    exact_mod_cast basic_prefix_denominator_pos hPH hτ.2.2.1
  have hq := prefixQ_bounds hPH hτ.2.2.1
  have hr := prefix_candidate_ratio hPH hτ.2.2.1
  calc
    _ = ((prefixCandidateFactor τ.tail : ℝ)/prefixDenominator τ.tail)*prefixQ τ.tail := by
      rw [hell]
      change ((tupleLeastCandidate (TotientTuple.mk τ.head τ.tail) : ℝ)/
        tupleValue (TotientTuple.mk τ.head τ.tail))*tupleQ τ=_
      rw [tupleLeastCandidate_eq_head,tupleValue_eq_head]
      change ((τ.head*prefixCandidateFactor τ.tail : ℕ) : ℝ)/
        (((τ.head-1)*prefixDenominator τ.tail : ℕ) : ℝ)*
          (prefixQ τ.tail*(1-(1 : ℝ)/τ.head))=_
      simp only [Nat.cast_mul,Nat.cast_sub hp.one_lt.le,Nat.cast_one]
      field_simp [hD.ne',sub_ne_zero.mpr hp1.ne', (zero_lt_one.trans hp1).ne']
    _ = _ := (eq_div_iff hq.1.ne').mp hr

/-- The product including the largest prime tends uniformly to one. -/
lemma full_prefix_defect {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ τ : TotientTuple (R x H), IsBasicTuple x H x τ →
        0<tupleQ τ ∧ 1-ε ≤ tupleQ τ ∧ tupleQ τ ≤ 1 := by
  have hi := tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ)<9/10))
  filter_upwards [prefix_reciprocal_sum,eventually_ge_atTop 2,
    prefixReciprocalError_tendsto.eventually (eventually_lt_nhds (show (0 : ℝ)<ε/2 by positivity))]
    with H hsum hH herr
  filter_upwards [theta_eventually_mem,m_tendsto.eventually (eventually_ge_atTop H),
    hi.eventually (eventually_lt_nhds (show (0 : ℝ)<ε/2 by positivity)),
    eventually_gt_atTop (0 : ℝ)] with x hs hm hx hx0
  simp only [Function.comp_def,← one_div] at hx
  intro τ hτ
  have hq := prefixQ_bounds (P_lt_self hH).le hτ.2.2.1
  have hsum := hsum x hs.1 hm τ.tail hτ.2.2.1
  have hp1 : (1 : ℝ)<τ.head := by exact_mod_cast hτ.1.one_lt
  have hp0 : (0 : ℝ)<τ.head := zero_lt_one.trans hp1
  have hpε : (1 : ℝ)/τ.head < ε/2 :=
    (one_div_le_one_div_of_le (Real.rpow_pos_of_pos hx0 _) hτ.2.1).trans_lt hx
  have hh : 0<1-(1 : ℝ)/τ.head := sub_pos.mpr ((div_lt_one hp0).mpr hp1)
  have hhle : 1-(1 : ℝ)/τ.head ≤ 1 := by
    linarith [div_nonneg zero_le_one hp0.le]
  refine ⟨mul_pos hq.1 hh,?_,?_⟩
  · dsimp [tupleQ]
    nlinarith [mul_nonneg (sub_nonneg.mpr hq.2.1) (div_nonneg zero_le_one hp0.le)]
  · exact (mul_le_mul_of_nonneg_left hhle hq.1.le).trans (by simpa using hq.2.1)

lemma fk_lower_on_interval {k : ℕ} {a b r : ℝ}
    (hka : (k : ℝ)<a) (ha : a≤r) (hrb : r≤b) :
    min 1 (a-k)/b ≤ fk k r := by
  have hr : 0<r := ((Nat.cast_nonneg k).trans_lt hka).trans_le ha
  have hb : 0<b := hr.trans_le hrb
  have hδ : 0 ≤ min 1 (a-k) := le_min zero_le_one (sub_pos.mpr hka).le
  by_cases hk1 : r≤k+1
  · rw [fk_eq_one_sub hr (hka.le.trans ha) hk1]
    have hh : min 1 (a-k)≤r-k := (min_le_right _ _).trans (by linarith)
    calc
      min 1 (a-k)/b ≤ min 1 (a-k)/r := div_le_div_of_nonneg_left hδ hr hrb
      _ ≤ (r-k)/r := div_le_div_of_nonneg_right hh hr.le
      _ = 1-k/r := by field_simp
  · rw [fk_eq_inv hr (le_of_not_ge hk1)]
    exact (div_le_div_of_nonneg_right (min_le_left _ _) hb.le).trans
      (one_div_le_one_div_of_le hr hrb)

end TotientAsymptotic

end

end OAI
