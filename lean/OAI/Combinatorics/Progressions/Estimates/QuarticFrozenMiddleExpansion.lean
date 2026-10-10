import OAI.Combinatorics.Progressions.Geometry.QuarticBoxOrbitFactors

namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

section Evaluation

variable {p q : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
  [TopologicalSpace (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
  [T2Space (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
  {N : ℕ} (i j : Fin W.outputDim)
  (R : NativePolynomialOrbitFactors (pi (fun _ : QuarticBoxFactor => W.model))
    (W.quarticAntisymmetricBoxPolynomial i j)
    (piFrequency W.quarticAntisymmetricBoxFrequencies) (fun _ : QuarticBoxIndex => (N : ℝ)) q)

theorem quartic_box_eval_factors (hp : 0 ≤ p) (n : QuarticBoxIndex → ℤ) :
    W.quarticAntisymmetricBoxValue i j n =
      (W.quarticAntisymmetricBoxNiltest hp i j).observable
        (QuotientGroup.mk (R.frozenMiddleValue (R.slowValue n) (R.rationalValue n) n)) := by
  rw [← W.quarticAntisymmetricBoxNiltest_eval hp]
  exact R.eval_niltest (W.quarticAntisymmetricBoxNiltest hp i j)
    (W.quarticAntisymmetricBoxPolynomial_eq_test hp i j) n

theorem quartic_box_top_layer_invariant (hp : 0 ≤ p)
    (z : (pi (fun _ : QuarticBoxFactor => W.model)).RealGroup)
    (hz : z.coord ∈ (pi (fun _ : QuarticBoxFactor => W.model)).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ _ : QuarticReplicatedIndex, 1))
    (x : (pi (fun _ : QuarticBoxFactor => W.model)).Space) :
    (W.quarticAntisymmetricBoxNiltest hp i j).observable (z • x) =
      (W.quarticAntisymmetricBoxNiltest hp i j).observable x := by
  have htop : z ∈ (pi (fun _ : QuarticBoxFactor => W.model)).filtration.realification.subgroup
      (∑ _ : QuarticReplicatedIndex, 1) :=
    (pi (fun _ : QuarticBoxFactor => W.model)).filtration.realGradedRefiltrationLayer_le R.subalgebra _ hz
  rw [W.quarticAntisymmetricBoxNiltest_vertical hp i j z htop, R.kills_top z.coord hz]
  simp only [AddCircle.coe_zero, CircleFourier.character_zero, one_mul]

theorem NativeMultidegreeNilcharacter.quarticAntisymmetricBoxNiltest_norm (hp : 0 ≤ p)
    (x : (pi (fun _ : QuarticBoxFactor => W.model)).Space) :
    ‖(W.quarticAntisymmetricBoxNiltest hp i j).observable x‖ ≤ 1 := by
  change ‖∏ a, (W.quarticAntisymmetricBoxFactors i j a).observable
    (productProjection (fun _ : QuarticBoxFactor => W.model) a x)‖ ≤ 1
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro a _
  simpa only [W.quarticAntisymmetricBoxFactors_normBound, NNReal.coe_one] using
    (W.quarticAntisymmetricBoxFactors i j a).norm_le
      (productProjection (fun _ : QuarticBoxFactor => W.model) a x)

end Evaluation

theorem exists_quartic_frozen_middle_expansion_of_bounds :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q u : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
      [TopologicalSpace (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
      [T2Space (ℝ ⊗[ℚ] (QuarticBoxFactor → W.L))]
      (hp : 0 ≤ p) {N : ℕ} [NeZero N] (i j : Fin W.outputDim)
      (R : NativePolynomialOrbitFactors (pi (fun _ : QuarticBoxFactor => W.model))
        (W.quarticAntisymmetricBoxPolynomial i j)
        (piFrequency W.quarticAntisymmetricBoxFrequencies) (fun _ : QuarticBoxIndex => (N : ℝ)) q),
      0 ≤ q → 0 ≤ u → ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.exp u →
      ∀ a r : (pi (fun _ : QuarticBoxFactor => W.model)).RealGroup,
        (∀ k, |((pi (fun _ : QuarticBoxFactor => W.model)).basis.baseChange ℝ).repr a.coord k| ≤ Real.exp u) →
        ((pi (fun _ : QuarticBoxFactor => W.model)).basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m →
        Nonempty (NativeIntegerExpansion (fun _ : QuarticBoxIndex => 1) 3 ((p + q + u + C) ^ C)
          (fun x => (W.quarticAntisymmetricBoxNiltest hp i j).observable
            (QuotientGroup.mk (R.frozenMiddleValue a r x)))) := by
  obtain ⟨c, _, hdesc⟩ := exists_native_frozen_middle_expansion 3
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + 32
  let T := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4 + X + 8
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro p q u W _ _ _ _ hp N _ i j R hq hu m hm hmb a r ha hrat
  let v := p + q + u
  let t := productNiltestBudget (v + 32) + v + 8
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hpv : p ≤ v := by dsimp only [v]; linarith only [hq, hu]
  have hqv : q ≤ v := by dsimp only [v]; linarith only [hp, hu]
  have huv : u ≤ v := le_add_of_nonneg_left (add_nonneg hp hq)
  have hprod : 0 ≤ productNiltestBudget (v + 32) := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hvt : v ≤ t := by dsimp only [t]; linarith only [hprod]
  have ht : 0 ≤ t := hv.trans hvt
  have hut : u ≤ t := huv.trans hvt
  have hmono : productNiltestBudget (p + 32) ≤ productNiltestBudget (v + 32) :=
    productNiltestBudget_mono (by positivity) (by linarith only [hpv])
  have htest : productNiltestBudget (p + 32) ≤ t := by
    dsimp only [t]
    linarith only [hmono, hv]
  let R' := R.mono (hqv.trans hvt) (fun _ => by exact_mod_cast NeZero.pos N)
  let S := W.quarticAntisymmetricBoxNiltest hp i j
  obtain ⟨E⟩ := hdesc (pi (fun _ : QuarticBoxFactor => W.model)) R' S ht
    ((W.quarticAntisymmetricBoxNiltest_complexity hp i j).mono htest)
    (quartic_box_top_layer_invariant W i j R' hp) m hm
    (hmb.trans (Real.exp_le_exp.mpr hut)) a r
    (fun k => (ha k).trans (Real.exp_le_exp.mpr hut)) hrat
  have hcost : (t + c) ^ c ≤ (p + q + u + C) ^ C := by
    simpa [X, Q, T, t, v, productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget v hv
  exact ⟨E.mono hcost⟩

end Erdos3

end

end OAI
