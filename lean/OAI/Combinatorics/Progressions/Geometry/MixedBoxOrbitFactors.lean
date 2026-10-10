import OAI.Combinatorics.Progressions.Estimates.MixedPairComparison
import OAI.Combinatorics.Progressions.Polynomial.MixedBoxPolynomial

namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_mixed_box_orbit_factors (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}, 0 ≤ q →
      ∀ (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      {N : ℕ} [NeZero N] (F : NativeMixedBoxFactorization W N q),
      Real.exp ((p + q + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativePolynomialOrbitFactors (pi (fun _ : MixedBoxFactor n => W.model))
        (W.mixedAntisymmetricBoxPolynomial F.leftIndex F.rightIndex)
        (piFrequency W.mixedAntisymmetricBoxFrequencies) (fun _ : MixedBoxIndex n => (N : ℝ))
        ((p + q + C) ^ C)) := by
  obtain ⟨a, _, horbit⟩ := exists_native_polynomial_orbit_factors (∑ _ : MixedReplicatedIndex (n + 1), 1)
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + 4 + Polynomial.C (2 ^ (n + 3))
  let R := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4 + X + Polynomial.C (2 * (n + 2))
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + (R + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q hq W N _ F hN
  have hp := F.nonnegative
  let := F.topology
  let := F.topologicalAdd
  let := F.continuousSMul
  let := F.hausdorff
  let D := pi (fun _ : MixedBoxFactor n => W.model)
  let g := W.mixedAntisymmetricBoxPolynomial F.leftIndex F.rightIndex
  let w := p + q
  let r := productNiltestBudget (mixedBoxBudget n w) + w + ((2 * (n + 2) : ℕ) : ℝ)
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hprod : 0 ≤ productNiltestBudget (mixedBoxBudget n w) := by
    unfold productNiltestBudget productObservableLipBudget mixedBoxBudget
    positivity
  have hdim : (0 : ℝ) ≤ ((2 * (n + 2) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hwr : w ≤ r := by
    dsimp only [r]
    linarith only [hprod, hdim]
  have hqr : q ≤ r := (by dsimp only [w]; linarith : q ≤ w).trans hwr
  have hdimr : ((2 * (n + 2) : ℕ) : ℝ) ≤ r := by dsimp only [r]; linarith only [hprod, hw]
  have hmono : productNiltestBudget (mixedBoxBudget n p) ≤ productNiltestBudget (mixedBoxBudget n w) :=
    productNiltestBudget_mono (by dsimp only [mixedBoxBudget]; positivity)
      (by dsimp only [mixedBoxBudget, w]; linarith)
  have hTr : productNiltestBudget (mixedBoxBudget n p) ≤ r :=
    hmono.trans (by dsimp only [r]; linarith only [hw, hdim])
  have hr : 0 ≤ r := hw.trans hwr
  have hcost : r + (r + a) ^ a ≤ (p + q + C) ^ C := by
    simpa [X, Q, R, r, w, mixedBoxBudget, productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget w hw
  have hfinal : (r + a) ^ a ≤ (p + q + C) ^ C := by linarith only [hcost, hr]
  have hgeom : D.GeometryComplexityLE r :=
    (W.mixedAntisymmetricBoxNiltest_complexity hp F.leftIndex F.rightIndex).1.mono D hTr
  have hfactor : D.filtration.ControlledSymbolFactorization F.basis F.weight F.adapted
      (piFrequency W.mixedAntisymmetricBoxFrequencies) (fun _ : MixedBoxIndex n => (N : ℝ))
      (D.filtration.realPolynomialSymbolHom F.basis F.weight F.adapted (fun _ => 1) g) r := by
    have h := F.factorization
    rw [W.mixedAntisymmetricBoxNiltest_symbol] at h
    have hNpos : ∀ _ : MixedBoxIndex n, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
    have H := NilpotentLieFiltration.ControlledSymbolFactorization.mono
      (pi (fun _ : MixedBoxFactor n => W.model)).filtration F.basis F.weight F.adapted h hqr hNpos
    dsimp only [D, g]
    exact H
  obtain ⟨U⟩ := horbit D F.basis F.weight F.adapted hr hgeom (by simpa [MixedBoxIndex, Nat.mul_comm] using hdimr)
    (fun i j => (F.height i j).trans hqr) g (piFrequency W.mixedAntisymmetricBoxFrequencies)
    (fun _ : MixedBoxIndex n => (N : ℝ)) (fun _ => (Real.exp_le_exp.mpr hfinal).trans hN) hfactor
  exact ⟨U.mono hfinal (fun _ => by exact_mod_cast NeZero.pos N)⟩

end Erdos3

end

end OAI
