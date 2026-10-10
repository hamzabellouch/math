import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.KernelWeight

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set

namespace OrdinaryCorrelations.Completion
open Finset ArithmeticFunction

def kernelConstant (σ : ℝ) : ℝ :=
  Real.exp ((2/(1-(2:ℝ)^(-σ))) * ∑' n : ℕ, (n:ℝ)^(-2*σ))

lemma base_ratio_lt_one {σ : ℝ} (hσ : 0 < σ) : (2:ℝ)^(-σ) < 1 := by
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) hσ)

lemma kernelWeight_prime_tsum_uniform {f : ℕ → ℂ} (hf : OneBounded f) (h1 : f 1 = 1)
    {σ : ℝ} (hσ : 0 < σ) {p : ℕ} (hp : Nat.Prime p) :
    (∑' k : ℕ, kernelWeight f σ (p^k)) ≤
      1 + (2/(1-(2:ℝ)^(-σ))) * (p:ℝ)^(-2*σ) := by
  have hrle : (p:ℝ)^(-σ) ≤ (2:ℝ)^(-σ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp.two_le) (by linarith)
  have hd : 0 < 1-(2:ℝ)^(-σ) := sub_pos.mpr (base_ratio_lt_one hσ)
  have he : ((p:ℝ)^(-σ))^2 = (p:ℝ)^(-2*σ) := by
    rw [←Real.rpow_mul_natCast (Nat.cast_nonneg p)]
    congr 1
    norm_num
    ring
  refine (kernelWeight_prime_tsum_le hf h1 hσ hp).trans (add_le_add (le_refl 1) ?_)
  calc
    2*((p:ℝ)^(-σ))^2/(1-(p:ℝ)^(-σ)) ≤
        2*((p:ℝ)^(-σ))^2/(1-(2:ℝ)^(-σ)) :=
      div_le_div_of_nonneg_left (by positivity) hd (by linarith)
    _ = (2/(1-(2:ℝ)^(-σ))) * (p:ℝ)^(-2*σ) := by rw [he]; ring

lemma kernelWeight_finite_euler_bound {f : ℕ → ℂ} (hf : OneBounded f) (h1 : f 1 = 1)
    {σ : ℝ} (hσ : 1/2 < σ) (s : Finset ℕ) :
    (∏ p ∈ s.filter Nat.Prime, ∑' k : ℕ, kernelWeight f σ (p^k)) ≤ kernelConstant σ := by
  have hσ0 : 0 < σ := by linarith
  let c := 2/(1-(2:ℝ)^(-σ))
  have hc : 0 ≤ c := div_nonneg (by norm_num) (le_of_lt (sub_pos.mpr (base_ratio_lt_one hσ0)))
  have hs : Summable (fun n : ℕ => (n:ℝ)^(-2*σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  calc
    (∏ p ∈ s.filter Nat.Prime, ∑' k : ℕ, kernelWeight f σ (p^k)) ≤
        ∏ p ∈ s.filter Nat.Prime, Real.exp (c*(p:ℝ)^(-2*σ)) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        exact tsum_nonneg (fun k => kernelWeight_nonneg _ _ _)
      · intro p hp
        exact (kernelWeight_prime_tsum_uniform hf h1 hσ0 (mem_filter.mp hp).2).trans
          (by simpa [add_comm] using Real.add_one_le_exp (c*(p:ℝ)^(-2*σ)))
    _ = Real.exp (c * ∑ p ∈ s.filter Nat.Prime, (p:ℝ)^(-2*σ)) := by
      rw [Finset.mul_sum,Real.exp_sum]
    _ ≤ kernelConstant σ := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hc
      exact hs.sum_le_tsum _ (fun n hn => Real.rpow_nonneg (Nat.cast_nonneg n) _)

lemma kernelWeight_sum_le {f : ℕ → ℂ} (hf : OneBounded f) (hm : Multiplicative f)
    (h1 : f 1 = 1) {σ : ℝ} (hσ : 1/2 < σ) (S : Finset ℕ) :
    (∑ n ∈ S, kernelWeight f σ n) ≤ kernelConstant σ := by
  classical
  let s := S.biUnion Nat.primeFactors
  have hσ0 : 0 < σ := by linarith
  have hlocal (p : ℕ) (hp : Nat.Prime p) :
      Summable (fun k : ℕ => ‖kernelWeight f σ (p^k)‖) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (kernelWeight_nonneg f σ _)] using
      kernelWeight_prime_summable hf h1 hσ0 hp
  have he := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (kernelWeight_one h1 σ) (fun {_ _} hc => kernelWeight_mul hm h1 σ hc)
    (fun {p} hp => hlocal p hp) s
  have hi : Summable ((Nat.factoredNumbers s).indicator (kernelWeight f σ)) := by
    apply summable_subtype_iff_indicator.mp
    exact he.1.of_norm
  have hi0 (n : ℕ) : 0 ≤ (Nat.factoredNumbers s).indicator (kernelWeight f σ) n := by
    by_cases hn : n ∈ Nat.factoredNumbers s
    · simpa [Set.indicator_of_mem hn] using kernelWeight_nonneg f σ n
    · simp [Set.indicator_of_notMem hn]
  calc
    (∑ n ∈ S, kernelWeight f σ n) ≤
        ∑ n ∈ S, (Nat.factoredNumbers s).indicator (kernelWeight f σ) n := by
      apply sum_le_sum
      intro n hn
      by_cases hn0 : n = 0
      · simp [hn0,hi0]
      have hns : n ∈ Nat.factoredNumbers s := by
        apply Nat.mem_factoredNumbers.mpr
        refine ⟨hn0, ?_⟩
        intro p hp
        apply mem_biUnion.mpr
        refine ⟨n,hn,?_⟩
        rcases (Nat.mem_primeFactorsList hn0).mp hp with ⟨hpp,hpn⟩
        exact Nat.mem_primeFactors.mpr ⟨hpp,hpn,hn0⟩
      simp [Set.indicator_of_mem hns]
    _ ≤ ∑' n : ℕ, (Nat.factoredNumbers s).indicator (kernelWeight f σ) n :=
      hi.sum_le_tsum S (fun n hn => hi0 n)
    _ = ∏ p ∈ s.filter Nat.Prime, ∑' k : ℕ, kernelWeight f σ (p^k) := by
      rw [←_root_.tsum_subtype]
      exact he.2.tsum_eq
    _ ≤ kernelConstant σ := kernelWeight_finite_euler_bound hf h1 hσ s

theorem kernelWeight_summable {f : ℕ → ℂ} (hf : OneBounded f) (hm : Multiplicative f)
    (h1 : f 1 = 1) {σ : ℝ} (hσ : 1/2 < σ) :
    Summable (kernelWeight f σ) ∧ (∑' n : ℕ, kernelWeight f σ n) ≤ kernelConstant σ := by
  have hs := summable_of_sum_le (fun n => kernelWeight_nonneg f σ n)
    (kernelWeight_sum_le hf hm h1 hσ)
  exact ⟨hs, hs.tsum_le_of_sum_le (kernelWeight_sum_le hf hm h1 hσ)⟩

end OrdinaryCorrelations.Completion

end

end OAI
