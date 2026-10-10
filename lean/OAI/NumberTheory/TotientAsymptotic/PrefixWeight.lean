import OAI.NumberTheory.TotientAsymptotic.PrefixReciprocals
import OAI.NumberTheory.TotientAsymptotic.WeightedFiber

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

def prefixQ {r : ℕ} (ζ : PrefixDatum r) : ℝ := ∏ i, (1-(1 : ℝ)/ζ.primes i)

lemma prefixQ_bounds {x : ℝ} {H : ℕ} (hPH : P H ≤ H)
    {ζ : PrefixDatum (R x H)} (hζ : IsPrefixDatum x H ζ) :
    0 < prefixQ ζ ∧ prefixQ ζ ≤ 1 ∧
      1-prefixQ ζ ≤ ∑ i, (1 : ℝ)/ζ.primes i := by
  have hp := (basic_prefix_data_positive hPH hζ).2
  have hi (i : Fin (R x H)) : 0 < 1-(1 : ℝ)/ζ.primes i ∧ 1-(1 : ℝ)/ζ.primes i ≤ 1 := by
    have hpi : (1 : ℝ) < ζ.primes i := by exact_mod_cast (hp i).one_lt
    constructor
    · exact sub_pos.mpr ((div_lt_one (zero_lt_one.trans hpi)).mpr hpi)
    · have : 0 ≤ (1 : ℝ)/ζ.primes i := by positivity
      linarith
  refine ⟨Finset.prod_pos (fun i _ => (hi i).1),Finset.prod_le_one₀ (fun i _ => (hi i).1.le) (fun i _ => (hi i).2),?_⟩
  have hh := one_sub_prod_le_sum Finset.univ (fun i => 1-(1 : ℝ)/ζ.primes i)
    (fun i _ => ⟨(hi i).1.le,(hi i).2⟩)
  simpa only [prefixQ,sub_sub_cancel] using hh

lemma prefix_candidate_ratio {x : ℝ} {H : ℕ} (hPH : P H ≤ H)
    {ζ : PrefixDatum (R x H)} (hζ : IsPrefixDatum x H ζ) :
    (prefixCandidateFactor ζ : ℝ)/prefixDenominator ζ =
      ((ell ζ.d : ℝ)/ζ.d)/prefixQ ζ := by
  have hp := (basic_prefix_data_positive hPH hζ).2
  have hq : prefixQ ζ=(∏ i, (ζ.primes i-1 : ℕ) : ℕ)/(∏ i, ζ.primes i : ℕ) := by
    simp only [prefixQ,Nat.cast_prod]
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i _
    have hpi : (0 : ℝ) < ζ.primes i := by exact_mod_cast (hp i).pos
    rw [Nat.cast_sub (hp i).one_lt.le,Nat.cast_one]
    field_simp
  have hpp : (0 : ℝ) < (∏ i, ζ.primes i : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => (hp i).pos)
  have hsp : (0 : ℝ) < (∏ i, (ζ.primes i-1) : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => Nat.sub_pos_of_lt (hp i).one_lt)
  have hd : (0 : ℝ) < ζ.d := by exact_mod_cast (basic_prefix_data_positive hPH hζ).1
  rw [hq,prefixCandidateFactor,prefixDenominator]
  push_cast
  field_simp

/-- The true interval weight is uniformly close to the arithmetic tail weight. -/
theorem prefix_weight_error : ∀ᶠ H : ℕ in atTop,
    ∀ x : ℝ, 0 ≤ theta x → H ≤ m x → ∀ k : ℕ,
    ∀ ζ : PrefixDatum (R x H), IsPrefixDatum x H ζ →
      |fk k ((prefixCandidateFactor ζ : ℝ)/prefixDenominator ζ)-fk k ((ell ζ.d : ℝ)/ζ.d)| ≤
        (2*(k : ℝ)+1)*prefixReciprocalError H := by
  filter_upwards [prefix_reciprocal_sum,eventually_ge_atTop 2] with H hsum hH
  intro x hs hm k ζ hζ
  have hPH := (P_lt_self hH).le
  have hq := prefixQ_bounds hPH hζ
  have hd : IsTotient ζ.d := by
    obtain ⟨η,hη,hd,_⟩ := hζ
    exact ⟨remainderTail x H η,suffixPreimage_pos (i := R x H) hη,hd⟩
  have hratio : 1 ≤ (ell ζ.d : ℝ)/ζ.d := one_le_ell_ratio hd
  rw [prefix_candidate_ratio hPH hζ]
  exact (fk_reciprocal_lipschitz k hratio hq.1 hq.2.1).trans
    (mul_le_mul_of_nonneg_left (hq.2.2.trans (hsum x hs hm ζ hζ)) (by positivity))

lemma prefix_ell_bound {x : ℝ} {H : ℕ} (hPH : P H < H) (hm : H ≤ m x)
    (hs : theta x ∈ Set.Ico (0 : ℝ) 1) {ζ : PrefixDatum (R x H)}
    (hζ : IsPrefixDatum x H ζ) : ell ζ.d ≤ tailValueBound H := by
  obtain ⟨η,hη,hd,_⟩ := hζ
  have hw := extractTail_isWitness hη hPH hm
  have hwd : (w (extractTail x H η)).totient=ζ.d := by
    rw [extractTail_value η hPH.le hm]
    exact hd
  exact (ell_le (witness_w_pos hw) hwd).trans (witness_w_bound hs hw)

lemma prefix_candidate_ratio_bounds : ∀ᶠ H : ℕ in atTop,
    ∀ x : ℝ, theta x ∈ Set.Ico (0 : ℝ) 1 → H ≤ m x →
    ∀ ζ : PrefixDatum (R x H), IsPrefixDatum x H ζ →
      1 ≤ (prefixCandidateFactor ζ : ℝ)/prefixDenominator ζ ∧
      (prefixCandidateFactor ζ : ℝ)/prefixDenominator ζ ≤ 2*tailValueBound H := by
  filter_upwards [prefix_reciprocal_sum,eventually_ge_atTop 2,
    prefixReciprocalError_tendsto.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/2))]
    with H hsum hH herr
  intro x hs hm ζ hζ
  have hPH := P_lt_self hH
  have hq := prefixQ_bounds hPH.le hζ
  have hqh : (1/2 : ℝ) ≤ prefixQ ζ := by
    have hh := hq.2.2.trans (hsum x hs.1 hm ζ hζ)
    linarith
  have hd := (prefix_tail_support hPH hm hs hζ).1
  have hr := one_le_ell_ratio hd
  have hd1 : (1 : ℝ) ≤ ζ.d := by exact_mod_cast isTotient_pos hd
  have hel : (ell ζ.d : ℝ) ≤ tailValueBound H := by exact_mod_cast prefix_ell_bound hPH hm hs hζ
  have hrbound : (ell ζ.d : ℝ)/ζ.d ≤ tailValueBound H :=
    (div_le_self (Nat.cast_nonneg _) hd1).trans hel
  rw [prefix_candidate_ratio hPH.le hζ]
  constructor
  · exact (one_le_div hq.1).mpr (hq.2.1.trans hr)
  · apply (div_le_iff₀ hq.1).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) (tailValueBound H)]

end TotientAsymptotic

end

end OAI
