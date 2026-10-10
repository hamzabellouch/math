import OAI.NumberTheory.Ostmann.Construction.TailSpectatorPool
import OAI.NumberTheory.Ostmann.Construction.TailBroadPriorBalance
import OAI.NumberTheory.Ostmann.Construction.InitialHalfListWeights
import OAI.NumberTheory.Ostmann.Construction.SupportedInitialLogSum
import OAI.NumberTheory.Ostmann.Construction.SpectatorBulkScale

namespace OAI

/-! # The two actual harmonic priors and their original cutoff centers -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem harmonic_prior_prime_bound (P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (a : ℝ) (ha : 0 < a) (hmass : a ≤ ∑ p ∈ Q, (p : ℝ)⁻¹) (p : P) :
    (p : ℝ) * primeSubsetPrior P Q p ≤ a⁻¹ := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p p.property).ne_zero
  calc
    _ ≤ (p : ℝ) * ((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * (p : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (primeSubsetPrior_atom P Q p) (Nat.cast_nonneg _)
    _ = (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ := by field_simp
    _ ≤ a⁻¹ := inv_anti₀ ha hmass

/-- The bulk center is chosen under its original harmonic prior and balanced
event. The spectator center uses the complete retained good-prime pool. Both
weights are kept as weights, before selecting any top or compensation cell. -/
theorem EventuallyPrimeSumset.initial_broad_prior_centers
    (hBonami : PublishedBonamiBound) (P0 : PublishedProgressionInput)
    (H : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve) (hsize : PublishedSummandSizeBound)
    {C : ℝ} (hM : MertensEstimate C)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (k cutoff : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ,
      Real.exp ((4 / 100 : ℝ) * L) ≤ Y → Y ≤ Real.exp L →
      ∀ hi : ℕ, (hi : ℝ) = Real.exp Y →
      ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp L →
      let Qb := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L)) \ D
      let m := spectatorBulkCount k L
      let good := fun p : ℕ => (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
        residueDensity (tailDensityMask A N p) ≤ 2 / 3
      ∃ Qd : Finset ℕ,
        Qd ⊆ primeLogCellSet 1 0 (Real.exp ((4 / 10000 : ℝ) * L))
          (Real.exp ((6 / 10000 : ℝ) * L)) \ D ∧
        L / 320000 ≤ ∑ p ∈ Qd, (p : ℝ)⁻¹ ∧
        (∀ p ∈ Qd, cutoff ≤ p ∧ good p ∧ tailCharacterBias A N p ≤ ε / 2) ∧
        ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → Qb ⊆ P → Qd ⊆ P →
          (∑ p : P, primeSubsetPrior P Qb p) = 1 ∧
          (∑ p : P, primeSubsetPrior P Qd p) = 1 ∧
          (∀ p : P, (p : ℝ) * primeSubsetPrior P Qb p ≤ (L / 320000)⁻¹ ∧
            (p : ℝ) * primeSubsetPrior P Qd p ≤ (L / 320000)⁻¹) ∧
          ∃ cb ∈ Finset.Icc (0 : ℤ) ⌈(m / 2 : ℕ) * Real.exp ((6 / 1000 : ℝ) * L)⌉₊,
          ∃ cd ∈ Finset.Icc (0 : ℤ) ⌈(m / 2 : ℕ) * Real.exp ((6 / 10000 : ℝ) * L)⌉₊,
            Real.exp (-(Real.log 2 + 2) * m) ≤
              ∑ x ∈ balancedTupleSet (m / 2) (fun _ (p : P) => good p),
                productPrior (fun _ => primeSubsetPrior P Qb) x *
                  initialLogSumWeight (fun p : P => (p : ℕ)) cb x ∧
            Real.exp (-(Real.log 2 + 2) * m) ≤
              ∑ x ∈ balancedTupleSet (m / 2) (fun _ (p : P) => good p),
                productPrior (fun _ => primeSubsetPrior P Qd) x *
                  initialLogSumWeight (fun p : P => (p : ℕ)) cd x := by
  classical
  obtain ⟨_a, _ha, hbalance⟩ := h.tail_broad_prior_balance hsize hA hB N hN C hM
  filter_upwards [hbalance,
    h.tail_spectator_pool hBonami P0 H hSiegel sieve hsize hM hA hB N hN cutoff ε hε,
    whole_shell_retained_linear_mass hM 1 (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hbalance hpool hmass hL
  intro Y hYlo hYhi hi hhi D hD Qb m good
  obtain ⟨Qd, hQd, hMd, hgood⟩ := hpool D hD
  have hMb : L / 16000 ≤ ∑ p ∈ Qb, (p : ℝ)⁻¹ :=
    hmass D (by simpa only [one_mul] using hD)
  have hsmall : L / 320000 ≤ ∑ p ∈ Qb, (p : ℝ)⁻¹ := by linarith only [hMb, hL]
  have hpos : 0 < L / 320000 := by positivity
  refine ⟨Qd, hQd, hMd, ?_, ?_⟩
  · intro p hp
    exact ⟨(hgood p hp).1, ⟨(hgood p hp).2.2.1, (hgood p hp).2.2.2.1⟩,
      (hgood p hp).2.2.2.2.1⟩
  · intro P hP hQbP hQdP
    have hbm := primeSubsetPrior_mass P Qb hQbP (hpos.trans_le hsmall).ne'
    have hdm := primeSubsetPrior_mass P Qd hQdP (hpos.trans_le hMd).ne'
    refine ⟨hbm, hdm, fun p => ⟨harmonic_prior_prime_bound P Qb hP _ hpos hsmall p,
      harmonic_prior_prime_bound P Qd hP _ hpos hMd p⟩, ?_⟩
    have hk4 : (16 : ℝ) ≤ (k : ℝ) ^ 4 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (show (2 : ℝ) ≤ (k : ℝ) from by exact_mod_cast hk) 4
      norm_num at hh
      exact hh
    have hscale : 4 ≤ (k : ℝ) ^ 4 * L := by nlinarith only [hk4, hL]
    have hLm : L ≤ (m : ℝ) := by
      have hh := spectatorBulkCount_half k L hscale
      change (k : ℝ) ^ 4 * L / 2 ≤ (m : ℝ) at hh
      nlinarith only [hh, hk4, hL]
    have hm : 1 ≤ m := by exact_mod_cast hL.trans hLm
    have hn : m / 2 ≤ m := Nat.div_le_self _ _
    have hlogb (i : Fin (m / 2)) (p : P) (hp : primeSubsetPrior P Qb p ≠ 0) :
        Real.log (p : ℝ) ≤ Real.exp ((6 / 1000 : ℝ) * L) :=
      (mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp (primeSubsetPrior_support P Qb p hp)).1).2.2.2
    have hlogd (i : Fin (m / 2)) (p : P) (hp : primeSubsetPrior P Qd p ≠ 0) :
        Real.log (p : ℝ) ≤ Real.exp ((6 / 10000 : ℝ) * L) :=
      (mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp
        (hQd (primeSubsetPrior_support P Qd p hp))).1).2.2.2
    have hb : (1 / 2 : ℝ) ≤ ∑ p : P, if good p then primeSubsetPrior P Qb p else 0 :=
      hbalance Y hYlo hYhi hi hhi D hD P hQbP
    have hd : (∑ p : P, if good p then primeSubsetPrior P Qd p else 0) = 1 := by
      calc
        _ = ∑ p : P, primeSubsetPrior P Qd p := by
          apply Finset.sum_congr rfl
          intro p _
          by_cases hp : primeSubsetPrior P Qd p = 0
          · simp only [hp, ite_self]
          · have hg := hgood p (primeSubsetPrior_support P Qd p hp)
            have hg' : good p := ⟨hg.2.2.1, hg.2.2.2.1⟩
            simp only [ite_eq_left hg']
        _ = 1 := hdm
    obtain ⟨cb, hcb, hbmass⟩ := exists_supported_prime_log_sum_center P hP (m / 2) m
      ((6 / 1000 : ℝ) * L) (fun _ => primeSubsetPrior P Qb) (fun _ p => good p)
      hm hn (by linarith only [hLm, hL]) hlogb (fun _ => by
        convert hb using 1
        apply Finset.sum_congr rfl
        intro p _
        by_cases hp : good p <;> simp only [hp, ite_true, ite_false])
    obtain ⟨cd, hcd, hdmass⟩ := exists_supported_prime_log_sum_center P hP (m / 2) m
      ((6 / 10000 : ℝ) * L) (fun _ => primeSubsetPrior P Qd) (fun _ p => good p)
      hm hn (by linarith only [hLm, hL]) hlogd (fun _ => by
        convert ((show (1 / 2 : ℝ) ≤ 1 by norm_num).trans (le_of_eq hd.symm)) using 1
        apply Finset.sum_congr rfl
        intro p _
        by_cases hp : good p <;> simp only [hp, ite_true, ite_false])
    exact ⟨cb, hcb, cd, hcd, hbmass, hdmass⟩

end Ostmann

end OAI
