import OAI.Algebra.DepthFive.CircuitFactorForms
import OAI.Algebra.DepthFive.CircuitStructure
import OAI.Algebra.DepthFive.CircuitRankAssembly

namespace OAI

open scoped BigOperators
noncomputable section

namespace Problem335
universe u v

/-- The product estimate required when every positive formal degree is small. -/
def LowProductBound {K : Type u} [CommSemiring K] {σ : Type v}
    (R : MvPolynomial σ K → ℝ) (d : ℕ) (t B : ℝ) : Prop :=
  ∀ factors : List (MvPolynomial σ K × ℕ),
    (∀ q ∈ factors, 0 < q.2 ∧ q.1.IsHomogeneous q.2 ∧ (q.2 : ℝ) < t) →
    (factors.map Prod.snd).sum = d →
    R (factors.map Prod.fst).prod ≤ B

/-- The product estimate required after opening one large middle factor. -/
def HighProductBound {K : Type u} [CommSemiring K] {σ : Type v}
    (R : MvPolynomial σ K → ℝ) (d : ℕ) (t B : ℝ) : Prop :=
  ∀ (linears : List (MvPolynomial σ K)) (others : List (MvPolynomial σ K × ℕ)),
    (∀ p ∈ linears, p.IsHomogeneous 1) →
    (∀ q ∈ others, 0 < q.2 ∧ q.1.IsHomogeneous q.2) →
    t ≤ (linears.length : ℝ) →
    linears.length + (others.map Prod.snd).sum = d →
    R (linears.prod * (others.map Prod.fst).prod) ≤ B

/-- Opening one high middle factor, or applying the all-low estimate, bounds
an actual list of positive-degree middle-gate occurrences. -/
theorem positive_middle_product_measure_le
    {K : Type u} [CommSemiring K] {n : ℕ} (c : Depth5Circuit K n)
    (R : MvPolynomial (Fin n × Fin n × Fin n) K → ℝ)
    (hzero : R 0 = 0) (hadd : ∀ x y, R (x + y) ≤ R x + R y)
    (hscale : ∀ a p, R (MvPolynomial.C a * p) ≤ R p)
    (d : ℕ) (t B : ℝ) (hB : 0 ≤ B)
    (hlow : LowProductBound R d t B) (hhigh : HighProductBound R d t B)
    (l : List (Fin c.middleCount))
    (hpos : ∀ j ∈ l, 0 < c.middleDegree j)
    (hdegree : (l.map c.middleDegree).sum = d) :
    R (l.map (middleValue c)).prod ≤ (circuitSize c : ℝ) * B := by
  classical
  have honeNat : 1 ≤ circuitSize c := by unfold circuitSize; omega
  have hone : (1 : ℝ) ≤ circuitSize c := by exact_mod_cast honeNat
  by_cases hsmall : ∀ j ∈ l, (c.middleDegree j : ℝ) < t
  · have hb := hlow (l.map fun j => (middleValue c j, c.middleDegree j)) (by
      intro q hq
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      exact ⟨hpos j hj, middleValue_isHomogeneous c j, hsmall j hj⟩) (by
      simpa only [List.map_map, Function.comp_def] using hdegree)
    have hb' : R (l.map (middleValue c)).prod ≤ B := by
      simpa only [List.map_map, Function.comp_def] using hb
    exact hb'.trans (by nlinarith)
  · push Not at hsmall
    obtain ⟨j, hj, hjhigh⟩ := hsmall
    obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp hj
    let others := (before ++ after).map fun k => (middleValue c k, c.middleDegree k)
    have hothers : ∀ q ∈ others, 0 < q.2 ∧ q.1.IsHomogeneous q.2 := by
      intro q hq
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
      refine ⟨hpos k ?_, middleValue_isHomogeneous c k⟩
      rcases List.mem_append.mp hk with hk | hk
      · exact List.mem_append_left _ hk
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hk)
    have htotal : c.middleDegree j + (others.map Prod.snd).sum = d := by
      simpa [others, List.map_append, List.sum_append, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm, Function.comp_def] using hdegree
    have hexpand :
        ((before ++ j :: after).map (middleValue c)).prod =
          ∑ k : Fin c.lowerCount,
            MvPolynomial.C (gateCoefficient (c.middleInputs j) k) *
              (lowerValue c k * (others.map Prod.fst).prod) := by
      simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
      rw [middleValue_eq_sum, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [others, List.map_map, Function.comp_def, List.map_append, List.prod_append]
      ring
    have hbranches : ∀ k : Fin c.lowerCount,
        gateCoefficient (c.middleInputs j) k ≠ 0 →
        R (lowerValue c k * (others.map Prod.fst).prod) ≤ B := by
      intro k hk
      have hkdegree := middleDegree_of_gateCoefficient_ne_zero c j k hk
      obtain ⟨a, linears, hlen, hlin, hval⟩ := lowerValue_normal_form c k
      have hlen' : linears.length = c.middleDegree j := hlen.trans hkdegree
      have heq : lowerValue c k * (others.map Prod.fst).prod =
          MvPolynomial.C a * (linears.prod * (others.map Prod.fst).prod) := by
        rw [hval]
        ring
      rw [heq]
      apply (hscale a _).trans
      exact hhigh linears others hlin hothers (by simpa [hlen'] using hjhigh)
        (by simpa [hlen'] using htotal)
    have hb : R (((before ++ j :: after).map (middleValue c)).prod) ≤
        (c.lowerCount : ℝ) * B := by
      rw [hexpand]
      simpa using measure_weighted_sum_le_card_mul R hzero hadd hscale Finset.univ
        (gateCoefficient (c.middleInputs j))
        (fun k => lowerValue c k * (others.map Prod.fst).prod) B hB
        (fun k _ => hbranches k)
    have hcountNat : c.lowerCount ≤ circuitSize c := by unfold circuitSize; omega
    have hcount : (c.lowerCount : ℝ) ≤ circuitSize c := by exact_mod_cast hcountNat
    exact hb.trans (mul_le_mul_of_nonneg_right hcount hB)

/-- The manuscript's gate-count reduction instantiated with the actual circuit
normal forms. All remaining hypotheses are bounds on homogeneous products,
not circuit-specific summands or wire counts. -/
theorem circuit_measure_le_of_product_estimates
    {K : Type u} [CommSemiring K] {n : ℕ} (c : Depth5Circuit K n)
    (R : MvPolynomial (Fin n × Fin n × Fin n) K → ℝ)
    (hzero : R 0 = 0) (hadd : ∀ x y, R (x + y) ≤ R x + R y)
    (hscale : ∀ a p, R (MvPolynomial.C a * p) ≤ R p)
    (d : ℕ) (houtput : c.outputDegree = d) (t B : ℝ) (hB : 0 ≤ B)
    (hlow : LowProductBound R d t B) (hhigh : HighProductBound R d t B) :
    R (circuitValue c) ≤ (circuitSize c : ℝ) ^ 2 * B := by
  have hSB : 0 ≤ (circuitSize c : ℝ) * B := mul_nonneg (Nat.cast_nonneg _) hB
  have hgates : ∀ u, gateCoefficient c.outputInputs u ≠ 0 →
      R (upperValue c u) ≤ (circuitSize c : ℝ) * B := by
    intro u hu
    obtain ⟨a, factors, _, hpos, hdegree, hval, _⟩ := upperValue_positive_factors c u
    have hdegree' : (factors.map c.middleDegree).sum = d :=
      hdegree.trans ((outputDegree_of_gateCoefficient_ne_zero c u hu).trans houtput)
    rw [hval]
    exact (hscale a _).trans
      (positive_middle_product_measure_le c R hzero hadd hscale d t B hB
        hlow hhigh factors hpos hdegree')
  have hcountNat : c.upperCount ≤ circuitSize c := by unfold circuitSize; omega
  have hcount : (c.upperCount : ℝ) ≤ circuitSize c := by exact_mod_cast hcountNat
  calc
    R (circuitValue c) ≤ (c.upperCount : ℝ) * ((circuitSize c : ℝ) * B) :=
      circuit_measure_le_upperCount_mul c R hzero hadd hscale _ hSB hgates
    _ ≤ (circuitSize c : ℝ) * ((circuitSize c : ℝ) * B) :=
      mul_le_mul_of_nonneg_right hcount hSB
    _ = (circuitSize c : ℝ) ^ 2 * B := by ring

end Problem335

end

end OAI
