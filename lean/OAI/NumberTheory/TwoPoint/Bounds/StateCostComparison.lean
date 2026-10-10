import OAI.NumberTheory.TwoPoint.Bounds.PaddingCutCircuit
import OAI.NumberTheory.TwoPoint.Bounds.PositivePrimeCostComparison

namespace OAI

/-! Exact finite-interval comparison for any bounded Q-state event,
including the literal density cutoff after the low-degree test. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem BravermanDepth22Input.eventually_state_cost_comparison
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M)
        (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (S : Finset ℕ), S ⊆ data.P ∪ data.Q → (S.card : ℝ) ≤ L ^ 2 →
      ∀ (q : ℕ), q ∈ retainedPrimeDivisors data.Q →
      (q.primeFactors.card : ℝ) ≤ 100 * Real.log L →
      ∀ (D : ℕ), (D : ℝ) ≤ 400 * Real.log L →
      ∀ (E : Finset (Fin (Fintype.card data.Q)) → Prop) (site : ℤ) (a N : ℕ),
      Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let F := fun n : ℤ => actualPaddingCoefficient q * positivePrimeWeight S (n + site) *
        if (q : ℤ) ∣ n + site ∧ actualPaddingDegree data.Q (n + site) ≤ D ∧
          E (paddingActiveState data.Q (Fintype.equivFin data.Q).symm (n + site))
          then 1 else 0
      |uniformAverage (fun x : Fin N => F (a + x.val)) -
        (data.residueLaw B hB).average (fun x => F (data.residueOrigin x))| ≤
          Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_positive_prime_cost_comparison
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (4800 : ℝ)] with L hb hL
  intro h J M B data hB hpool hBL S hS hSL q hq hqdegree D hD E site a N hN
  let U := data.P ∪ data.Q
  let hQU : data.Q ⊆ U := subset_union_right
  let literal : Fin (Fintype.card U) → U × ℤ :=
    fun i => ((Fintype.equivFin U).symm i, site)
  let index := primeSubsetIndex U S hS
  let qindex := primeSubsetIndex U data.Q hQU
  let dindex := primeSubsetIndex U q.primeFactors
    ((retainedPrimeDivisor_factors data.Q data.primeQ hq).trans hQU)
  let c := stateDivisorCircuit qindex dindex D E
  let bad := fun n : ℤ => (q : ℤ) ∣ n + site ∧ actualPaddingDegree data.Q (n + site) ≤ D ∧
    E (paddingActiveState data.Q (Fintype.equivFin data.Q).symm (n + site))
  have hindex (i : Fin (Fintype.card S)) :
      (literal (index i)).1.val = ((Fintype.equivFin S).symm i).val ∧
        (literal (index i)).2 = site :=
    ⟨primeSubsetIndex_value U S hS i, rfl⟩
  have hQcard : (Fintype.card data.Q : ℝ) ≤ Real.exp L := by
    have hbound : data.Q.card ≤ B := (card_le_card hQU).trans
      (primePool_card_bound U (fun p hp => data.prime ⟨p, hp⟩) B hB)
    have hbound' : (data.Q.card : ℝ) ≤ B := by exact_mod_cast hbound
    simpa only [Fintype.card_coe] using hbound'.trans hBL
  have hqcard : (Fintype.card q.primeFactors : ℝ) ≤ 100 * Real.log L := by
    simpa only [Fintype.card_coe] using hqdegree
  have hsize : (c.size : ℝ) ≤ Real.exp (L ^ 3) :=
    stateDivisorCircuit_size_exp qindex dindex D E L hL hQcard hqcard hD
  have hc : c.depth ≤ 19 := (stateDivisorCircuit_depth qindex dindex D E).trans (by norm_num)
  have hbad (n : ℤ) : c.eval
      (fun i => decide (((literal i).1.val : ℤ) ∣ n + (literal i).2)) = true ↔ bad n :=
    stateDivisorCircuit_integer U data.Q hQU data.primeQ q hq D E (n + site)
  have hh := hb h J M B data hB hpool hBL S hS hSL q.primeFactors.card
    (Fintype.card U) hqdegree literal index site hindex c hc hsize bad hbad a N hN
  simpa [actualPaddingCoefficient, bad] using hh

theorem BravermanDepth22Input.eventually_density_cost_comparison
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M)
        (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (S : Finset ℕ), S ⊆ data.P ∪ data.Q → (S.card : ℝ) ≤ L ^ 2 →
      ∀ (q : ℕ), q ∈ retainedPrimeDivisors data.Q →
      (q.primeFactors.card : ℝ) ≤ 100 * Real.log L →
      ∀ (D : Finset ℕ), D ⊆ retainedPrimeDivisors data.Q →
      ∀ (eligible : ℕ → Prop) (K : ℝ) (site : ℤ) (a N : ℕ),
      Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let F := fun n : ℤ => actualPaddingCoefficient q * positivePrimeWeight S (n + site) *
        if (q : ℤ) ∣ n + site ∧ actualPaddingDegreeCut data.Q L (n + site) ∧
          K / L < paddingDensity D actualPaddingCoefficient eligible
            (actualPaddingVertex data.Q) (n + site) then 1 else 0
      |uniformAverage (fun x : Fin N => F (a + x.val)) -
        (data.residueLaw B hB).average (fun x => F (data.residueOrigin x))| ≤
          Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_state_cost_comparison
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with L hb hL
  intro h J M B data hB hpool hBL S hS hSL q hq hqdegree D hD eligible K site a N hN
  have hlog : 0 ≤ 400 * Real.log L :=
    mul_nonneg (by norm_num) (Real.log_nonneg hL)
  let E := fun T : Finset (Fin (Fintype.card data.Q)) =>
    K / L < paddingStateDensity data.Q D (Fintype.equivFin data.Q).symm eligible T
  have hh := hb h J M B data hB hpool hBL S hS hSL q hq hqdegree
    ⌊400 * Real.log L⌋₊ (Nat.floor_le hlog) E site a N hN
  have he (n : ℤ) : (actualPaddingDegree data.Q n ≤ ⌊400 * Real.log L⌋₊ ∧
      E (paddingActiveState data.Q (Fintype.equivFin data.Q).symm n)) ↔
      (actualPaddingDegreeCut data.Q L n ∧
        K / L < paddingDensity D actualPaddingCoefficient eligible (actualPaddingVertex data.Q) n) := by
    rw [Nat.le_floor_iff hlog, paddingDensity_eq_state data.Q D data.primeQ hD
      (Fintype.equivFin data.Q).symm eligible n]
    rfl
  simpa only [he] using hh

end TwoPointCorrelations

end OAI
