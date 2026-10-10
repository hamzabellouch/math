import OAI.NumberTheory.TwoPoint.Bounds.PrimeDegreeCircuit
import OAI.NumberTheory.TwoPoint.Bounds.PositivePrimeCostComparison

namespace OAI

/-! Finite-interval transfer of the literal prime-degree deletion.
The padding-divisor indicator is kept, so its reciprocal saving is
available in the residue-model bound. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem BravermanDepth22Input.eventually_degree_cost_comparison
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M)
        (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (S V : Finset ℕ), S ⊆ data.P ∪ data.Q → V ⊆ data.P ∪ data.Q →
      (S.card : ℝ) ≤ L ^ 2 →
      ∀ (q : ℕ), q ∈ retainedPrimeDivisors data.Q →
      (q.primeFactors.card : ℝ) ≤ 100 * Real.log L →
      ∀ (T : ℝ), 0 ≤ T → T ≤ 400 * Real.log L →
      ∀ (site : ℤ) (a N : ℕ), Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let F := fun n : ℤ => actualPaddingCoefficient q * positivePrimeWeight S (n + site) *
        if (q : ℤ) ∣ n + site ∧ T < (actualPaddingDegree V (n + site) : ℝ) then 1 else 0
      |uniformAverage (fun x : Fin N => F (a + x.val)) -
        (data.residueLaw B hB).average (fun x => F (data.residueOrigin x))| ≤
          Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_positive_prime_cost_comparison
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (4800 : ℝ)] with L hb hL
  intro h J M B data hB hpool hBL S V hS hV hSL q hq hqdegree T hT hTL site a N hN
  let U := data.P ∪ data.Q
  let hQU : data.Q ⊆ U := subset_union_right
  let literal : Fin (Fintype.card U) → U × ℤ :=
    fun i => ((Fintype.equivFin U).symm i, site)
  let index := primeSubsetIndex U S hS
  let pindex := primeSubsetIndex U V hV
  let qindex := primeSubsetIndex U q.primeFactors
    ((retainedPrimeDivisor_factors data.Q data.primeQ hq).trans hQU)
  let c := degreeDivisorCircuit pindex qindex (⌊T⌋₊ + 1)
  let bad := fun n : ℤ => (q : ℤ) ∣ n + site ∧
    T < (actualPaddingDegree V (n + site) : ℝ)
  have hindex (i : Fin (Fintype.card S)) :
      (literal (index i)).1.val = ((Fintype.equivFin S).symm i).val ∧
        (literal (index i)).2 = site :=
    ⟨primeSubsetIndex_value U S hS i, rfl⟩
  have hVcard : (Fintype.card V : ℝ) ≤ Real.exp L := by
    have hbound : V.card ≤ B := (card_le_card hV).trans
      (primePool_card_bound U (fun p hp => data.prime ⟨p, hp⟩) B hB)
    have hbound' : (V.card : ℝ) ≤ B := by exact_mod_cast hbound
    simpa only [Fintype.card_coe] using hbound'.trans hBL
  have hqcard : (Fintype.card q.primeFactors : ℝ) ≤ 100 * Real.log L := by
    simpa only [Fintype.card_coe] using hqdegree
  have hfloor : ((⌊T⌋₊ + 1 : ℕ) : ℝ) ≤ 400 * Real.log L + 1 := by
    push_cast
    linarith [Nat.floor_le hT]
  have hsize : (c.size : ℝ) ≤ Real.exp (L ^ 3) :=
    degreeDivisorCircuit_size_exp pindex qindex (⌊T⌋₊ + 1) L hL hVcard hqcard hfloor
  have hc : c.depth ≤ 19 := (degreeDivisorCircuit_depth pindex qindex _).trans (by norm_num)
  have hbad (n : ℤ) : c.eval
      (fun i => decide (((literal i).1.val : ℤ) ∣ n + (literal i).2)) = true ↔ bad n :=
    degreeDivisorCircuit_integer U V data.Q hV hQU data.primeQ q hq T hT (n + site)
  have hh := hb h J M B data hB hpool hBL S hS hSL q.primeFactors.card
    (Fintype.card U) hqdegree literal index site hindex c hc hsize bad hbad a N hN
  simpa [actualPaddingCoefficient, bad] using hh

end TwoPointCorrelations

end OAI
