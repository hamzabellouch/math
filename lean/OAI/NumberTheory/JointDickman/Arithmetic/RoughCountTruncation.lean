import OAI.NumberTheory.JointDickman.Arithmetic.RoughCountPrefix

namespace OAI

/-! # Removing irrelevant primes above the prefix cutoff -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

lemma finitePrimeDivisorCount_truncate (P : Finset ℕ) (N n : ℕ)
    (hn : 0 < n) (hnN : n ≤ N) :
    finitePrimeDivisorCount (P.filter (fun p => p ≤ N)) n =
      finitePrimeDivisorCount P n := by
  unfold finitePrimeDivisorCount
  rw [sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases hd : p ∣ n
  · simp [hd,Nat.le_of_dvd hn hd |>.trans hnN]
  · simp [hd]

theorem rough_count_prefix_unrestricted {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    {ε : ℝ} (hε : 0 < ε) : ∃ T : ℝ, 0 < T ∧
    ∀ᶠ N : ℕ in atTop, ∀ (f : ArithmeticFunction ℂ) (P : Finset ℕ),
      f.IsMultiplicative → (∀ n, ‖f n‖ ≤ 1) →
      (∀ p k : ℕ, p.Prime → (p:ℝ) ≤ (N:ℝ)^c → p^k ≤ N → f (p^k) = 1) →
      (∀ p ∈ P, p.Prime ∧ (N:ℝ)^c < (p:ℝ)) →
      ∀ t : ℝ, T ≤ |t| → |t| ≤ 4*(Real.log N)^8 →
      ‖∑ n ∈ Icc 1 N, (f n*halaszPowerPhase t n)/
        ((finitePrimeDivisorCount P n:ℂ)+1)‖/(N:ℝ) ≤ ε := by
  obtain ⟨T,hT,hprefix⟩ := rough_count_prefix_away_zero hc hc1 hε
  refine ⟨T,hT,?_⟩
  filter_upwards [hprefix] with N hN
  intro f P hf hfb hlocal hP t htlo hthi
  have hh := hN f (P.filter (fun p => p ≤ N)) hf hfb hlocal
    (fun p hp => ⟨(hP p (mem_filter.mp hp).1).1,
      (hP p (mem_filter.mp hp).1).2,by exact_mod_cast (mem_filter.mp hp).2⟩) t htlo hthi
  convert hh using 1
  congr 2
  apply sum_congr rfl
  intro n hn
  rw [finitePrimeDivisorCount_truncate P N n (mem_Icc.mp hn).1 (mem_Icc.mp hn).2]

end JointDickman

end OAI
