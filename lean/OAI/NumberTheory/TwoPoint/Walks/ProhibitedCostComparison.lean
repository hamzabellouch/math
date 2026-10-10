import OAI.NumberTheory.TwoPoint.Walks.ProhibitedWordCircuit
import OAI.NumberTheory.TwoPoint.Bounds.PositivePrimeCostComparison
import OAI.NumberTheory.TwoPoint.Bounds.PrimeDegreeCircuit

namespace OAI

/-! Positive costs at actual prohibited sites. The forbidden-word DNF
is conjoined with the padding divisor test on a shared list of prime
literals; all circuit bounds are derived here. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def prohibitedCostCircuit {n m t : ℕ} (c : AC0Circuit n)
    (index : Fin n → Fin m) (qindex : Fin t → Fin m) : AC0Circuit m :=
  AC0Circuit.conjunction (fun b : Bool => if b then c.relabel index else
    (degreeSubsetCircuit univ).relabel qindex)

lemma prohibitedCostCircuit_eval {n m t : ℕ} (c : AC0Circuit n)
    (index : Fin n → Fin m) (qindex : Fin t → Fin m) (x : BooleanCube m) :
    (prohibitedCostCircuit c index qindex).eval x = true ↔
      (∀ i, x (qindex i) = true) ∧ c.eval (fun i => x (index i)) = true := by
  rw [prohibitedCostCircuit, AC0Circuit.conjunction_eval]
  simp only [Bool.forall_bool, Bool.false_eq_true, ite_false, ite_true,
    AC0Circuit.relabel_eval, degreeSubsetCircuit_eval]
  have he : (univ : Finset (Fin t)) ⊆ activeState (fun i => x (qindex i)) ↔
      ∀ i, x (qindex i) = true := by
    simp only [subset_iff, mem_univ, activeState, mem_filter, true_and, forall_const]
  rw [he]

lemma prohibitedCostCircuit_depth {n m t : ℕ} (c : AC0Circuit n)
    (index : Fin n → Fin m) (qindex : Fin t → Fin m) (hc : c.depth ≤ 2) :
    (prohibitedCostCircuit c index qindex).depth ≤ 3 := by
  apply AC0Circuit.conjunction_depth
  intro b
  cases b
  · exact (AC0Circuit.relabel_depth _ _).trans ((degreeSubsetCircuit_depth _).trans (by omega))
  · exact (AC0Circuit.relabel_depth _ _).trans hc

lemma prohibitedCostCircuit_size {n m t : ℕ} (c : AC0Circuit n)
    (index : Fin n → Fin m) (qindex : Fin t → Fin m) :
    (prohibitedCostCircuit c index qindex).size ≤ 2 + t + c.size := by
  rw [prohibitedCostCircuit, AC0Circuit.conjunction_size]
  simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true]
  have hq := AC0Circuit.relabel_size qindex (degreeSubsetCircuit (univ : Finset (Fin t)))
  have hp := AC0Circuit.relabel_size index c
  simp only [degreeSubsetCircuit_size, card_univ, Fintype.card_fin] at hq
  omega

lemma prohibitedCostCircuit_size_exp {n m t : ℕ} (c : AC0Circuit n)
    (index : Fin n → Fin m) (qindex : Fin t → Fin m) (L : ℝ)
    (hL : 4800 ≤ L) (ht : (t : ℝ) ≤ 100 * Real.log L)
    (hc : (c.size : ℝ) ≤ Real.exp (104 * L ^ 2)) :
    ((prohibitedCostCircuit c index qindex).size : ℝ) ≤ Real.exp (L ^ 3) := by
  have hlog : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hraw : ((prohibitedCostCircuit c index qindex).size : ℝ) ≤ 2 + t + c.size := by
    exact_mod_cast prohibitedCostCircuit_size c index qindex
  have hsmall : 2 + (t : ℝ) ≤ Real.exp (104 * L ^ 2) := by
    have he := Real.add_one_le_exp (104 * L ^ 2)
    nlinarith [sq_nonneg (L - 1)]
  calc
    _ ≤ 2 * Real.exp (104 * L ^ 2) := by linarith
    _ ≤ Real.exp (1 + 104 * L ^ 2) := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos _).le
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hsq : (1 : ℝ) ≤ L ^ 2 := by nlinarith
      have hh := mul_nonneg (sq_nonneg L) (show 0 ≤ L - 105 by linarith)
      nlinarith)

/-- One actual positive tuple/padding cost at a prohibited origin is
compared with its value under the same residue law as the graph. -/
theorem BravermanDepth22Input.eventually_prohibited_cost_comparison
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B s cap : ℕ) (data : ProhibitedPrimeFamily h J M)
        (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      (s : ℝ) ≤ L → (cap : ℝ) ≤ L ^ 2 →
      (data.pairs.card : ℝ) ≤ Real.exp (101 * L) →
      (∀ dq ∈ data.pairs, (dq.2 * dq.1).primeFactors.card ≤ cap) →
      ∀ (S : Finset ℕ), S ⊆ data.P ∪ data.Q → (S.card : ℝ) ≤ L ^ 2 →
      ∀ (q : ℕ), q ∈ retainedPrimeDivisors data.Q →
      (q.primeFactors.card : ℝ) ≤ 100 * Real.log L →
      ∀ (site : ℤ) (a N : ℕ), Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let F := fun n : ℤ => actualPaddingCoefficient q * positivePrimeWeight S (n + site) *
        if (q : ℤ) ∣ n + site ∧
          ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (n + site) then 1 else 0
      |uniformAverage (fun x : Fin N => F (a + x.val)) -
        (data.residueLaw B hB).average (fun x => F (data.residueOrigin x))| ≤
          Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_positive_prime_cost_comparison
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (4800 : ℝ)] with L hb hL
  intro h J M B s cap data hB hpool hBL hs hcap hpair hdegree S hS hSL q hq hqdegree site a N hN
  let U := data.P ∪ data.Q
  let n := Fintype.card (ProhibitedInputs data.pairs h s)
  let I := Fin n ⊕ Fin (Fintype.card U)
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let cindex : Fin n → Fin (Fintype.card I) := fun i => e (Sum.inl i)
  let uindex : Fin (Fintype.card U) → Fin (Fintype.card I) := fun i => e (Sum.inr i)
  let literal : Fin (Fintype.card I) → U × ℤ := fun i =>
    Sum.elim (fun j => ((data.prohibitedLiteral s j).1, site + (data.prohibitedLiteral s j).2))
      (fun j => ((Fintype.equivFin U).symm j, site)) (e.symm i)
  let index : Fin (Fintype.card S) → Fin (Fintype.card I) :=
    fun i => uindex (primeSubsetIndex U S hS i)
  let qindex : Fin (Fintype.card q.primeFactors) → Fin (Fintype.card I) :=
    fun i => uindex (primeSubsetIndex U q.primeFactors
      ((retainedPrimeDivisor_factors data.Q data.primeQ hq).trans subset_union_right) i)
  let c := prohibitedCostCircuit (prohibitedCircuit data.pairs h s) cindex qindex
  let bad := fun n : ℤ => (q : ℤ) ∣ n + site ∧
    ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (n + site)
  have hindex (i : Fin (Fintype.card S)) :
      (literal (index i)).1.val = ((Fintype.equivFin S).symm i).val ∧
        (literal (index i)).2 = site := by
    simp only [literal, index, uindex, Equiv.symm_apply_apply, Sum.elim_inr]
    exact ⟨primeSubsetIndex_value U S hS i, trivial⟩
  have hbad (n0 : ℤ) : c.eval
      (fun i => decide (((literal i).1.val : ℤ) ∣ n0 + (literal i).2)) = true ↔ bad n0 := by
    rw [prohibitedCostCircuit_eval]
    have hqbits : (∀ i, decide (((literal (qindex i)).1.val : ℤ) ∣
        n0 + (literal (qindex i)).2) = true) ↔ (q : ℤ) ∣ n0 + site := by
      simpa only [literal, qindex, uindex, Equiv.symm_apply_apply, Sum.elim_inr,
        primeSiteBits] using
        prime_divisor_all_bits U data.Q subset_union_right data.primeQ q hq (n0 + site)
    have hcbits : (fun i => decide (((literal (cindex i)).1.val : ℤ) ∣
        n0 + (literal (cindex i)).2)) = prohibitedInputAt data.pairs h s (n0 + site) := by
      funext i
      have hi := data.prohibitedLiteral_integer_input s (n0 + site) i
      rw [primeLiteral_integer_input] at hi
      simpa only [literal, cindex, Equiv.symm_apply_apply, Sum.elim_inl, add_assoc] using hi
    rw [hqbits, hcbits, prohibitedCircuit_correct data.pairs h s (n0 + site) data.whole_squarefree]
  have hsize : (c.size : ℝ) ≤ Real.exp (L ^ 3) := by
    apply prohibitedCostCircuit_size_exp _ _ _ L hL
    · simpa only [Fintype.card_coe] using hqdegree
    · exact prohibitedCircuit_size_quadratic data.pairs h s cap L (by linarith)
        hs hcap hpair hdegree
  have hc : c.depth ≤ 19 :=
    (prohibitedCostCircuit_depth _ _ _ (prohibitedCircuit_depth data.pairs h s)).trans (by omega)
  have hh := hb h J M B data hB hpool hBL S hS hSL q.primeFactors.card
    (Fintype.card I) hqdegree literal index site hindex c hc hsize bad hbad a N hN
  simpa [actualPaddingCoefficient, bad] using hh

end TwoPointCorrelations

end OAI
