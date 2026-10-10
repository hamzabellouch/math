import OAI.Combinatorics.Progressions.Estimates.MixedPairComparison
import OAI.Combinatorics.Progressions.Polynomial.QuarticBoxPolynomial

namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_quartic_box_orbit_factors :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}, 0 ≤ q →
      ∀ (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
      {N : ℕ} [NeZero N] (F : NativeQuarticBoxFactorization W N q),
      Real.exp ((p + q + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativePolynomialOrbitFactors (pi (fun _ : QuarticBoxFactor => W.model))
        (W.quarticAntisymmetricBoxPolynomial F.leftIndex F.rightIndex)
        (piFrequency W.quarticAntisymmetricBoxFrequencies) (fun _ : QuarticBoxIndex => (N : ℝ))
        ((p + q + C) ^ C)) := by
  obtain ⟨a, _, horbit⟩ := exists_native_polynomial_orbit_factors (∑ _ : QuarticReplicatedIndex, 1)
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + 32
  let R := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4 + X + 8
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + (R + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q hq W N _ F hN
  have hp := F.nonnegative
  let := F.topology
  let := F.topologicalAdd
  let := F.continuousSMul
  let := F.hausdorff
  let D := pi (fun _ : QuarticBoxFactor => W.model)
  let g := W.quarticAntisymmetricBoxPolynomial F.leftIndex F.rightIndex
  let w := p + q
  let r := productNiltestBudget (w + 32) + w + 8
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hprod : 0 ≤ productNiltestBudget (w + 32) := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hwr : w ≤ r := by dsimp only [r]; linarith only [hprod]
  have hqr : q ≤ r := (by dsimp only [w]; linarith : q ≤ w).trans hwr
  have h8r : 8 ≤ r := by dsimp only [r]; linarith only [hprod, hw]
  have hmono : productNiltestBudget (p + 32) ≤ productNiltestBudget (w + 32) :=
    productNiltestBudget_mono (by positivity) (by dsimp only [w]; linarith)
  have hTr : productNiltestBudget (p + 32) ≤ r := hmono.trans (by dsimp only [r]; linarith only [hw])
  have hr : 0 ≤ r := hw.trans hwr
  have hcost : r + (r + a) ^ a ≤ (p + q + C) ^ C := by
    simpa [X, Q, R, r, w, productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget w hw
  have hfinal : (r + a) ^ a ≤ (p + q + C) ^ C := by linarith only [hcost, hr]
  have hgeom : D.GeometryComplexityLE r :=
    (W.quarticAntisymmetricBoxNiltest_complexity hp F.leftIndex F.rightIndex).1.mono D hTr
  have hfactor : D.filtration.ControlledSymbolFactorization F.basis F.weight F.adapted
      (piFrequency W.quarticAntisymmetricBoxFrequencies) (fun _ : QuarticBoxIndex => (N : ℝ))
      (D.filtration.realPolynomialSymbolHom F.basis F.weight F.adapted (fun _ => 1) g) r := by
    have h := F.factorization
    rw [W.quarticAntisymmetricBoxNiltest_symbol] at h
    have hNpos : ∀ _ : QuarticBoxIndex, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
    have H := NilpotentLieFiltration.ControlledSymbolFactorization.mono
      (pi (fun _ : QuarticBoxFactor => W.model)).filtration F.basis F.weight F.adapted h hqr hNpos
    dsimp only [D, g]
    exact H
  obtain ⟨U⟩ := horbit D F.basis F.weight F.adapted hr hgeom (by simpa [QuarticBoxIndex] using h8r)
    (fun i j => (F.height i j).trans hqr) g (piFrequency W.quarticAntisymmetricBoxFrequencies)
    (fun _ : QuarticBoxIndex => (N : ℝ)) (fun _ => (Real.exp_le_exp.mpr hfinal).trans hN) hfactor
  exact ⟨U.mono hfinal (fun _ => by exact_mod_cast NeZero.pos N)⟩

end Erdos3

end

end OAI
