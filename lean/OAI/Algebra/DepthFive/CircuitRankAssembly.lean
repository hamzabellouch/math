import OAI.Algebra.DepthFive.GateSums

namespace OAI

open scoped BigOperators
noncomputable section

namespace Problem335

/-- Finite subadditivity, with no assumptions on the individual summands. -/
theorem measure_finset_sum_le {A ι : Type*} [AddCommMonoid A]
    (R : A → ℝ) (hzero : R 0 = 0)
    (hadd : ∀ x y, R (x + y) ≤ R x + R y)
    (s : Finset ι) (f : ι → A) :
    R (∑ j ∈ s, f j) ≤ ∑ j ∈ s, R (f j) := by
  classical
  induction s using Finset.induction with
  | empty => simp [hzero]
  | @insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      exact (hadd _ _).trans (add_le_add le_rfl ih)

/-- Scalar weighting cannot increase a subadditive rank-like measure. -/
theorem measure_weighted_sum_le {K σ ι : Type*} [CommSemiring K]
    (R : MvPolynomial σ K → ℝ) (hzero : R 0 = 0)
    (hadd : ∀ x y, R (x + y) ≤ R x + R y)
    (hscale : ∀ a p, R (MvPolynomial.C a * p) ≤ R p)
    (s : Finset ι) (a : ι → K) (p : ι → MvPolynomial σ K) :
    R (∑ j ∈ s, MvPolynomial.C (a j) * p j) ≤ ∑ j ∈ s, R (p j) := by
  exact (measure_finset_sum_le R hzero hadd s _).trans
    (Finset.sum_le_sum (fun j _ => hscale (a j) (p j)))

/-- Expand one selected factor and leave all other occurrences unchanged.
This is the algebraic step behind the high-degree-factor case: in particular,
other occurrences of the very same middle gate are not expanded. -/
theorem measure_one_factor_expansion_le {K σ ι : Type*} [CommSemiring K]
    (R : MvPolynomial σ K → ℝ) (hzero : R 0 = 0)
    (hadd : ∀ x y, R (x + y) ≤ R x + R y)
    (hscale : ∀ a p, R (MvPolynomial.C a * p) ≤ R p)
    (s : Finset ι) (a : ι → K) (p : ι → MvPolynomial σ K)
    (before after : MvPolynomial σ K) :
    R (before * (∑ j ∈ s, MvPolynomial.C (a j) * p j) * after) ≤
      ∑ j ∈ s, R (before * p j * after) := by
  have heq :
      before * (∑ j ∈ s, MvPolynomial.C (a j) * p j) * after =
        ∑ j ∈ s, MvPolynomial.C (a j) * (before * p j * after) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq]
  exact measure_weighted_sum_le R hzero hadd hscale s a _

/-- Only predecessors with nonzero aggregate coefficient need a bound.
This matters for homogeneous circuits, since inactive gates can have arbitrary
formal degree. -/
theorem measure_weighted_sum_le_card_mul {K σ ι : Type*} [CommSemiring K]
    (R : MvPolynomial σ K → ℝ) (hzero : R 0 = 0)
    (hadd : ∀ x y, R (x + y) ≤ R x + R y)
    (hscale : ∀ a p, R (MvPolynomial.C a * p) ≤ R p)
    (s : Finset ι) (a : ι → K) (p : ι → MvPolynomial σ K)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ j ∈ s, a j ≠ 0 → R (p j) ≤ B) :
    R (∑ j ∈ s, MvPolynomial.C (a j) * p j) ≤ (s.card : ℝ) * B := by
  calc
    R (∑ j ∈ s, MvPolynomial.C (a j) * p j) ≤
        ∑ j ∈ s, R (MvPolynomial.C (a j) * p j) :=
      measure_finset_sum_le R hzero hadd s _
    _ ≤ ∑ j ∈ s, B := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases ha : a j = 0
      · simpa [ha, hzero] using hB
      · exact (hscale _ _).trans (hbound j hj ha)
    _ = (s.card : ℝ) * B := by simp

/-- A uniform bound on active output predecessors costs the number of upper
product gates, never the number of output wires. -/
theorem circuit_measure_le_upperCount_mul {K : Type*} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n)
    (R : MvPolynomial (Fin n × Fin n × Fin n) K → ℝ) (hzero : R 0 = 0)
    (hadd : ∀ x y, R (x + y) ≤ R x + R y)
    (hscale : ∀ a p, R (MvPolynomial.C a * p) ≤ R p)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ j, gateCoefficient c.outputInputs j ≠ 0 → R (upperValue c j) ≤ B) :
    R (circuitValue c) ≤ (c.upperCount : ℝ) * B := by
  rw [circuitValue_eq_sum]
  simpa using measure_weighted_sum_le_card_mul R hzero hadd hscale
    Finset.univ (gateCoefficient c.outputInputs) (upperValue c) B hB
    (fun j _ => hbound j)

/-- Expanding one middle-gate occurrence costs at most the number of lower
product gates. All other occurrences, including shared copies of the selected
gate, are retained as factors in `before` and `after`. -/
theorem upper_measure_le_lowerCount_mul_of_split
    {K : Type*} [CommSemiring K] {n : ℕ} (c : Depth5Circuit K n)
    (R : MvPolynomial (Fin n × Fin n × Fin n) K → ℝ) (hzero : R 0 = 0)
    (hadd : ∀ x y, R (x + y) ≤ R x + R y)
    (hscale : ∀ a p, R (MvPolynomial.C a * p) ≤ R p)
    (u : Fin c.upperCount) (j : Fin c.middleCount)
    (before after : List (Fin c.middleCount))
    (hsplit : c.upperInputs u = before ++ j :: after)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ l, gateCoefficient (c.middleInputs j) l ≠ 0 →
      R ((before.map (middleValue c)).prod * lowerValue c l *
        (after.map (middleValue c)).prod) ≤ B) :
    R (upperValue c u) ≤ (c.lowerCount : ℝ) * B := by
  classical
  have heq : upperValue c u =
      ∑ l : Fin c.lowerCount,
        MvPolynomial.C (gateCoefficient (c.middleInputs j) l) *
          ((before.map (middleValue c)).prod * lowerValue c l *
            (after.map (middleValue c)).prod) := by
    unfold upperValue
    rw [hsplit]
    simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
    rw [middleValue_eq_sum, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [heq]
  simpa using measure_weighted_sum_le_card_mul R hzero hadd hscale
    Finset.univ (gateCoefficient (c.middleInputs j))
    (fun l => (before.map (middleValue c)).prod * lowerValue c l *
      (after.map (middleValue c)).prod) B hB (fun l _ => hbound l)

/-- The gate-count assembly step in the depth-five rank upper bound.
Each active upper product is either bounded directly, or one occurrence can
be expanded into active lower products with the same bound. -/
theorem circuit_measure_le_size_sq_mul_of_low_or_split
    {K : Type*} [CommSemiring K] {n : ℕ} (c : Depth5Circuit K n)
    (R : MvPolynomial (Fin n × Fin n × Fin n) K → ℝ) (hzero : R 0 = 0)
    (hadd : ∀ x y, R (x + y) ≤ R x + R y)
    (hscale : ∀ a p, R (MvPolynomial.C a * p) ≤ R p)
    (B : ℝ) (hB : 0 ≤ B)
    (hupper : ∀ u, gateCoefficient c.outputInputs u ≠ 0 →
      R (upperValue c u) ≤ B ∨
        ∃ (j : Fin c.middleCount) (before after : List (Fin c.middleCount)),
          c.upperInputs u = before ++ j :: after ∧
          ∀ l, gateCoefficient (c.middleInputs j) l ≠ 0 →
            R ((before.map (middleValue c)).prod * lowerValue c l *
              (after.map (middleValue c)).prod) ≤ B) :
    R (circuitValue c) ≤ (circuitSize c : ℝ) ^ 2 * B := by
  have honeNat : 1 ≤ circuitSize c := by unfold circuitSize; omega
  have hlowerNat : c.lowerCount ≤ circuitSize c := by unfold circuitSize; omega
  have hupperNat : c.upperCount ≤ circuitSize c := by unfold circuitSize; omega
  have hone : (1 : ℝ) ≤ circuitSize c := by exact_mod_cast honeNat
  have hlower : (c.lowerCount : ℝ) ≤ circuitSize c := by exact_mod_cast hlowerNat
  have hupperCount : (c.upperCount : ℝ) ≤ circuitSize c := by exact_mod_cast hupperNat
  have hSB : 0 ≤ (circuitSize c : ℝ) * B := mul_nonneg (Nat.cast_nonneg _) hB
  have hgates : ∀ u, gateCoefficient c.outputInputs u ≠ 0 →
      R (upperValue c u) ≤ (circuitSize c : ℝ) * B := by
    intro u hu
    rcases hupper u hu with hlow | ⟨j, before, after, hsplit, hbound⟩
    · exact hlow.trans (by nlinarith)
    · exact (upper_measure_le_lowerCount_mul_of_split c R hzero hadd hscale
        u j before after hsplit B hB hbound).trans (mul_le_mul_of_nonneg_right hlower hB)
  calc
    R (circuitValue c) ≤ (c.upperCount : ℝ) * ((circuitSize c : ℝ) * B) :=
      circuit_measure_le_upperCount_mul c R hzero hadd hscale _ hSB hgates
    _ ≤ (circuitSize c : ℝ) * ((circuitSize c : ℝ) * B) :=
      mul_le_mul_of_nonneg_right hupperCount hSB
    _ = (circuitSize c : ℝ) ^ 2 * B := by ring

end Problem335

end

end OAI
