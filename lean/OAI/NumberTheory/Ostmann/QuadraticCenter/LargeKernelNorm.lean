import OAI.NumberTheory.Ostmann.Construction.DyadicShellBudget

namespace OAI

/-! # The large-kernel norm of the original positive quadratic series -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

/-- The `.006 + o(1)` bound over the full large-kernel range. The coefficient
family is the original compactly supported quadratic series, and the dyadic
decomposition and all residue estimates are supplied by proved lemmas. -/
theorem eventual_large_kernel_positive_norm (C₀ H ε : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hC₀ : 0 ≤ C₀) (hH : 0 ≤ H) (hε : 0 < ε) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (M : ℕ) (S : Finset ℕ) (u : ℝ),
      (∀ p ∈ P, 10000 ≤ p) → (M : ℝ) ≤ Real.exp (C₀ * T) →
      (P.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, 4 * P.toList.prod ^ 2 ≤ s ∧ s ≤ M) →
      (∀ s ∈ S, P.toList.prod.Coprime s) → 2 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p))
        (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
        (R v : ℝ) (c : Finset ℕ → ℂ),
      0 < R → 0 < v → (∀ U ∈ P.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) →
      Real.sqrt (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖∑ U ∈ P.powerset, c U * primeDivisorPositive P hP D a θ Φ R v U s‖ ^ 2) ≤
        Real.exp ((3 / 500 + ε) * T ^ (9999999 / 10000000 : ℝ)) := by
  have hdy := eventual_dyadic_positive_norm (C₀ + 1) H (ε / 2) Φ hH (by positivity) hΦ
  have hcount := eventual_dyadic_shell_budget C₀ ε hC₀ hε
  filter_upwards [hdy, hcount, eventually_ge_atTop (1 : ℝ)] with T hdy hcount hT
  intro P hP M S u hlarge hM hcard hS hrange hcop hu huU D a θ R v c hR hv hc
  let K := T ^ (9999999 / 10000000 : ℝ)
  let f := fun s : ℕ => (u ^ s.primeFactors.card / (s : ℝ)) *
    ‖∑ U ∈ P.powerset, c U * primeDivisorPositive P hP D a θ Φ R v U s‖ ^ 2
  have hu0 : 0 ≤ u := by linarith
  have hf : ∀ s, 0 ≤ f s := by intro s; dsimp [f]; positivity
  have hL : 0 < P.toList.prod := prime_list_prod_pos _ (primeSet_list_prime P hP)
  have hs2 (s : ℕ) (hs : s ∈ S) : 2 ≤ s := by
    have hh := (hrange s hs).1
    nlinarith
  have htwo : (2 : ℝ) ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
  have hsegment (j : ℕ) :
      (∑ s ∈ S.filter (fun s => dyadicKernelShell s = j), f s) ≤
        Real.exp (2 * (3 / 500 + ε / 2) * K) := by
    let Sj := S.filter (fun s => dyadicKernelShell s = j)
    by_cases hne : Sj.Nonempty
    · obtain ⟨s₀, hs₀⟩ := hne
      obtain ⟨hs₀S, hj⟩ := Finset.mem_filter.mp hs₀
      have hjL : 2 * P.toList.prod ^ 2 ≤ 2 ^ j := by
        simpa only [hj] using dyadicKernelShell_modulus P.toList.prod s₀ (hrange s₀ hs₀S).1 (hs2 s₀ hs₀S)
      have hNM : 2 ^ j ≤ M := by
        have hh := (Finset.mem_Ioc.mp (dyadicKernelShell_mem s₀ (hs2 s₀ hs₀S))).1.le
        rw [hj] at hh
        exact hh.trans (hrange s₀ hs₀S).2
      have hcut : (2 * (2 ^ j) : ℝ) ≤ Real.exp ((C₀ + 1) * T) := by
        calc
          _ ≤ 2 * (M : ℝ) := by exact_mod_cast Nat.mul_le_mul_left 2 hNM
          _ ≤ 2 * Real.exp (C₀ * T) := mul_le_mul_of_nonneg_left hM (by norm_num)
          _ ≤ Real.exp T * Real.exp (C₀ * T) :=
            mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
          _ = _ := by rw [← Real.exp_add]; congr 1; ring
      have hSj (s : ℕ) (hs : s ∈ Sj) : s ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j) := by
        obtain ⟨hs, he⟩ := Finset.mem_filter.mp hs
        simpa only [he] using dyadicKernelShell_mem s (hs2 s hs)
      have hn := hdy P hP (2 ^ j) Sj u hlarge (by positivity) hjL (by
          simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul] using hcut)
        hcard (fun s hs => hS s (Finset.mem_filter.mp hs).1) hSj
        (fun s hs => hcop s (Finset.mem_filter.mp hs).1) hu huU D a θ R v c hR hv hc
      have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) hn 2
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun s _ => hf s)), ← Real.exp_nat_mul] at hh
      simpa only [Nat.cast_ofNat, mul_assoc, K, Sj] using hh
    · have he : Sj = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      change (∑ s ∈ Sj, f s) ≤ _
      rw [he, Finset.sum_empty]
      positivity
  have htotal : (∑ s ∈ S, f s) ≤ Real.exp (2 * (3 / 500 + ε) * K) := by
    rw [sum_dyadicKernelShells S M (fun s hs => (hrange s hs).2) f]
    calc
      _ ≤ ∑ _j ∈ Finset.range (Nat.log 2 M + 1), Real.exp (2 * (3 / 500 + ε / 2) * K) :=
        Finset.sum_le_sum (fun j _ => hsegment j)
      _ = (Nat.log 2 M + 1 : ℝ) * Real.exp (2 * (3 / 500 + ε / 2) * K) := by simp
      _ ≤ Real.exp (ε * K) * Real.exp (2 * (3 / 500 + ε / 2) * K) :=
        mul_le_mul_of_nonneg_right (hcount M hM) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply (Real.sqrt_le_sqrt htotal).trans_eq
  rw [← Real.exp_half]
  congr 1
  ring

end Ostmann

end OAI
