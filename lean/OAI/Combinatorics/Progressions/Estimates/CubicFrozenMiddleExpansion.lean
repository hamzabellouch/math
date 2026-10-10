import OAI.Combinatorics.Progressions.Geometry.CubicBoxOrbitFactors

namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

section Evaluation

variable {p q : ℝ} (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
  [TopologicalSpace (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
  [T2Space (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
  {N : ℕ} (i j : Fin V.outputDim × Fin V.outputDim) (shift : ℤ)
  (R : NativePolynomialOrbitFactors (pi (fun _ : Fin 8 × Fin 4 => V.model))
    (V.cubicAntisymmetricBoxPolynomial i j shift)
    (piFrequency V.cubicAntisymmetricBoxFrequencies) (fun _ : Fin 6 => (N : ℝ)) q)

theorem cubic_box_eval_factors (hp : 0 ≤ p) (n : Fin 6 → ℤ) :
    V.cubicAntisymmetricBoxValue i j shift n =
      (V.cubicAntisymmetricBoxNiltest hp i j shift).observable
        (QuotientGroup.mk (R.frozenMiddleValue (R.slowValue n) (R.rationalValue n) n)) := by
  rw [← V.cubicAntisymmetricBoxNiltest_eval hp]
  exact R.eval_niltest (V.cubicAntisymmetricBoxNiltest hp i j shift)
    (V.cubicAntisymmetricBoxPolynomial_eq_test hp i j shift) n

theorem cubic_box_top_layer_invariant (hp : 0 ≤ p)
    (z : (pi (fun _ : Fin 8 × Fin 4 => V.model)).RealGroup)
    (hz : z.coord ∈ (pi (fun _ : Fin 8 × Fin 4 => V.model)).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ _ : CubicReplicatedIndex, 1))
    (x : (pi (fun _ : Fin 8 × Fin 4 => V.model)).Space) :
    (V.cubicAntisymmetricBoxNiltest hp i j shift).observable (z • x) =
      (V.cubicAntisymmetricBoxNiltest hp i j shift).observable x := by
  have htop : z ∈ (pi (fun _ : Fin 8 × Fin 4 => V.model)).filtration.realification.subgroup
      (∑ _ : CubicReplicatedIndex, 1) :=
    (pi (fun _ : Fin 8 × Fin 4 => V.model)).filtration.realGradedRefiltrationLayer_le R.subalgebra _ hz
  rw [V.cubicAntisymmetricBoxNiltest_vertical hp i j shift z htop, R.kills_top z.coord hz]
  simp only [AddCircle.coe_zero, CircleFourier.character_zero, one_mul]

end Evaluation

theorem exists_cubic_frozen_middle_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
      [TopologicalSpace (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
      [T2Space (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
      (hp : 0 ≤ p) {N : ℕ} [NeZero N] (i j : Fin V.outputDim × Fin V.outputDim) (shift : ℤ)
      (R : NativePolynomialOrbitFactors (pi (fun _ : Fin 8 × Fin 4 => V.model))
        (V.cubicAntisymmetricBoxPolynomial i j shift)
        (piFrequency V.cubicAntisymmetricBoxFrequencies) (fun _ : Fin 6 => (N : ℝ)) p),
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.exp p →
      ∀ a r : (pi (fun _ : Fin 8 × Fin 4 => V.model)).RealGroup,
        (∀ k, |((pi (fun _ : Fin 8 × Fin 4 => V.model)).basis.baseChange ℝ).repr a.coord k| ≤ Real.exp p) →
        ((pi (fun _ : Fin 8 × Fin 4 => V.model)).basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m →
        Nonempty (NativeIntegerExpansion (fun _ : Fin 6 => 1) 2 ((p + C) ^ C)
          (fun x => (V.cubicAntisymmetricBoxNiltest hp i j shift).observable
            (QuotientGroup.mk (R.frozenMiddleValue a r x)))) := by
  obtain ⟨c, _, hdesc⟩ := exists_native_frozen_middle_expansion 2
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + 32
  let P := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4 + X + 6
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro p V _ _ _ _ hp N _ i j shift R m hm hmb a r ha hrat
  let t := productNiltestBudget (p + 32) + p + 6
  have hprod : 0 ≤ productNiltestBudget (p + 32) := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hpt : p ≤ t := by dsimp only [t]; linarith only [hprod]
  have hTt : productNiltestBudget (p + 32) ≤ t := by dsimp only [t]; linarith only [hp]
  have ht : 0 ≤ t := hp.trans hpt
  let R' := R.mono hpt (fun _ => by exact_mod_cast NeZero.pos N)
  let T := V.cubicAntisymmetricBoxNiltest hp i j shift
  obtain ⟨E⟩ := hdesc (pi (fun _ : Fin 8 × Fin 4 => V.model)) R' T ht
    ((V.cubicAntisymmetricBoxNiltest_complexity hp i j shift).mono hTt)
    (cubic_box_top_layer_invariant V i j shift R' hp) m hm
    (hmb.trans (Real.exp_le_exp.mpr hpt)) a r
    (fun k => (ha k).trans (Real.exp_le_exp.mpr hpt)) hrat
  have hcost : (t + c) ^ c ≤ (p + C) ^ C := by
    simpa [X, Q, P, t, productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget p hp
  exact ⟨E.mono hcost⟩

end Erdos3

end

end OAI
