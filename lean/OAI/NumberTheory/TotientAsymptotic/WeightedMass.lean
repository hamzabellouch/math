import OAI.NumberTheory.TotientAsymptotic.WeightedPrimeCount
import OAI.NumberTheory.TotientAsymptotic.PrefixWeight
import OAI.NumberTheory.TotientAsymptotic.TupleCoefficient

namespace OAI

noncomputable section
open scoped BigOperators Topology Classical
open Filter
namespace TotientAsymptotic

def candidateMass (x : ℝ) (H k : ℕ) : ℝ :=
  ∑ ζ ∈ prefixDataFinset x H,
    fk k ((prefixCandidateFactor ζ : ℝ)/prefixDenominator ζ)/(prefixDenominator ζ : ℝ)

lemma mass_eq_prefix_denominators (x : ℝ) (H : ℕ) (f : ℝ → ℝ) :
    M x H f = ∑ ζ ∈ prefixDataFinset x H,
      f ((ell ζ.d : ℝ)/ζ.d)/(prefixDenominator ζ : ℝ) := by
  rw [mass_eq_sum_prefixData]
  simp only [prefixDenominator,Nat.cast_mul,Nat.cast_prod]

lemma candidate_mass_perturbation : ∀ᶠ H : ℕ in atTop,
    ∀ x : ℝ, 0 ≤ theta x → H ≤ m x → ∀ k : ℕ,
      |candidateMass x H k-M x H (fk k)| ≤
        ((2*(k : ℝ)+1)*prefixReciprocalError H)*M x H (fun _ => 1) := by
  filter_upwards [prefix_weight_error,eventually_ge_atTop 2] with H he hH
  intro x hs hm k
  rw [candidateMass,mass_eq_prefix_denominators,mass_eq_prefix_denominators,
    ← Finset.sum_sub_distrib,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro ζ hζ
  have hz := mem_prefixDataFinset.mp hζ
  have hd : (0 : ℝ) < prefixDenominator ζ := by
    exact_mod_cast basic_prefix_denominator_pos (P_lt_self hH).le hz
  rw [← sub_div,abs_div,abs_of_pos hd]
  exact (div_le_div_of_nonneg_right (he x hs hm k ζ hz) hd.le).trans_eq (by ring)

/-- Summation of the actual least-preimage prime intervals, before replacing
its prefix ratio by the tail ratio. -/
theorem candidate_prime_mass_relative (hpnt : PrimeNumberTheoremInput) :
    ∀ᶠ H : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
      ∀ k : ℕ, 1 ≤ k →
      |((candidateTuples x H k).card : ℝ)-(x/Real.log x)*candidateMass x H k| ≤
        ε*(x/Real.log x)*M x H (fun _ => 1) := by
  filter_upwards [prefix_candidate_ratio_bounds,eventually_ge_atTop 2,
    P_tendsto.eventually (eventually_ge_atTop 1)] with H hratio hH hP
  intro ε hε
  let C : ℝ := max 1 (2*tailValueBound H)
  filter_upwards [weighted_prime_count hpnt (C := C) (le_max_left _ _) hε,
    basic_prefix_denominator_log_small (P_lt_self hH) hP,
    theta_eventually_mem,m_tendsto.eventually (eventually_ge_atTop H),
    eventually_gt_atTop (1 : ℝ)] with x hcount hlog hs hm hx
  intro k hk
  rw [candidate_count_eq_prime_fibers (P_lt_self hH).le (zero_lt_one.trans hx).le,
    candidateMass,mass_eq_prefix_denominators,Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro ζ hζ
  have hz := mem_prefixDataFinset.mp hζ
  have hd := basic_prefix_denominator_pos (P_lt_self hH).le hz
  have hdR : (0 : ℝ) < prefixDenominator ζ := by exact_mod_cast hd
  obtain ⟨hlo,hhi⟩ := hratio x hs hm ζ hz
  have hDA : prefixDenominator ζ ≤ prefixCandidateFactor ζ := by
    exact_mod_cast (one_le_div hdR).mp hlo
  have hAC : (prefixCandidateFactor ζ : ℝ) ≤ C*prefixDenominator ζ :=
    (div_le_iff₀ hdR).mp (hhi.trans (le_max_right _ _))
  have hc := hcount k (prefixDenominator ζ) (prefixCandidateFactor ζ) hk hd hDA hAC (hlog ζ hz)
  change |((candidatePrimeSet x H k ζ).card : ℝ)-_| ≤ _
  change |((intervalHeads x k (prefixDenominator ζ) (prefixCandidateFactor ζ)).card : ℝ)-_| ≤ _
  have heq : (x/Real.log x)*(fk k ((prefixCandidateFactor ζ : ℝ)/prefixDenominator ζ)/
      (prefixDenominator ζ : ℝ))=
      (x/(prefixDenominator ζ*Real.log x))*fk k ((prefixCandidateFactor ζ : ℝ)/prefixDenominator ζ) := by ring
  rw [heq]
  convert hc using 1
  ring

/-- The weighted counting error vanishes with the discrete tail cutoff. -/
theorem candidate_mass_normalized (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
        |((candidateTuples x H k).card : ℝ)/tupleNormalization x-
          M x H (fk k)/G x (m x)| ≤ δ H+ε := by
  obtain ⟨C,hC,hupper⟩ := mass_upper hbox hren hmertens
  let K := fun H => C*Real.exp ((4*(lam/rho))*cofactorScale H)
  let δ := fun H => (2*(k : ℝ)+1)*K H*prefixReciprocalError H
  have hK (H : ℕ) : 0 < K H := mul_pos hC (Real.exp_pos _)
  refine ⟨δ,?_,?_⟩
  · have ht := (weighted_prefixReciprocalError_tendsto (4*(lam/rho))).const_mul ((2*(k : ℝ)+1)*C)
    simp only [mul_zero] at ht
    convert ht using 1
    ext H
    dsimp [δ,K]
    ring
  filter_upwards [candidate_prime_mass_relative hpnt,candidate_mass_perturbation,hupper]
    with H hprime hpert hupper
  intro ε hε
  filter_upwards [hprime (ε/K H) (div_pos hε (hK H)),hupper,theta_eventually_mem,
    m_tendsto.eventually (eventually_ge_atTop H),eventually_gt_atTop (1 : ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hp hu hs hm hx hB
  have hG := G_pos hB (m x)
  have ht : 0 < x/Real.log x := div_pos (zero_lt_one.trans hx) (Real.log_pos hx)
  have hN := tupleNormalization_pos hx hB
  have hM : M x H (fun _ => 1) ≤ K H*G x (m x) := hu _ (fun _ => le_rfl)
  have he : |((candidateTuples x H k).card : ℝ)/tupleNormalization x-
      candidateMass x H k/G x (m x)| ≤ ε := by
    rw [show ((candidateTuples x H k).card : ℝ)/tupleNormalization x-candidateMass x H k/G x (m x)=
      (((candidateTuples x H k).card : ℝ)-(x/Real.log x)*candidateMass x H k)/tupleNormalization x by
        unfold tupleNormalization; field_simp [(Real.log_pos hx).ne',hG.ne'],
      abs_div,abs_of_pos hN]
    apply (div_le_iff₀ hN).mpr
    calc
      _ ≤ (ε/K H)*(x/Real.log x)*M x H (fun _ => 1) := hp k hk
      _ ≤ (ε/K H)*(x/Real.log x)*(K H*G x (m x)) :=
        mul_le_mul_of_nonneg_left hM (by positivity)
      _ = ε*tupleNormalization x := by unfold tupleNormalization; field_simp [(hK H).ne']
  have hmerr : |candidateMass x H k/G x (m x)-M x H (fk k)/G x (m x)| ≤ δ H := by
    rw [← sub_div,abs_div,abs_of_pos hG]
    apply (div_le_iff₀ hG).mpr
    exact (hpert x hs.1 hm k).trans ((mul_le_mul_of_nonneg_left hM
      (mul_nonneg (by positivity) (prefixReciprocalError_nonneg H))).trans_eq (by dsimp [δ]; ring))
  exact (abs_sub_le _ _ _).trans ((add_le_add he hmerr).trans_eq (add_comm _ _))

end TotientAsymptotic

end

end OAI
