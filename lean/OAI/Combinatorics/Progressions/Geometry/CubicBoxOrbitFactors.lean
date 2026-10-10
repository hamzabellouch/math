import OAI.Combinatorics.Progressions.Estimates.CubicFactoredModel

namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_cubic_box_orbit_factors :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
      {N : ℕ} [NeZero N] (F : NativeCubicBoxFactorization V N p),
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativePolynomialOrbitFactors (pi (fun _ : Fin 8 × Fin 4 => V.model))
        (V.cubicAntisymmetricBoxPolynomial F.leftIndex F.rightIndex (-(if F.branch then (N : ℤ) else 0)))
        (piFrequency V.cubicAntisymmetricBoxFrequencies) (fun _ : Fin 6 => (N : ℝ)) ((p + C) ^ C)) := by
  obtain ⟨a, _, horbit⟩ := exists_native_polynomial_orbit_factors (∑ _ : CubicReplicatedIndex, 1)
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + 32
  let R := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4 + X + 6
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + (R + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p V N _ F hN
  have hp := F.nonnegative
  let := F.topology
  let := F.topologicalAdd
  let := F.continuousSMul
  let := F.hausdorff
  let D := pi (fun _ : Fin 8 × Fin 4 => V.model)
  let g := V.cubicAntisymmetricBoxPolynomial F.leftIndex F.rightIndex (-(if F.branch then (N : ℤ) else 0))
  let r := productNiltestBudget (p + 32) + p + 6
  have hprod : 0 ≤ productNiltestBudget (p + 32) := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hpr : p ≤ r := by dsimp only [r]; linarith only [hprod]
  have h6r : 6 ≤ r := by dsimp only [r]; linarith only [hprod, hp]
  have hTr : productNiltestBudget (p + 32) ≤ r := by dsimp only [r]; linarith only [hp]
  have hr : 0 ≤ r := hp.trans hpr
  have hcost : r + (r + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Q, R, r, productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget p hp
  have hfinal : (r + a) ^ a ≤ (p + C) ^ C := by linarith only [hcost, hr]
  have hgeom : D.GeometryComplexityLE r :=
    (V.cubicAntisymmetricBoxNiltest_complexity hp F.leftIndex F.rightIndex
      (-(if F.branch then (N : ℤ) else 0))).1.mono D hTr
  have hfactor : D.filtration.ControlledSymbolFactorization F.basis F.weight F.adapted
      (piFrequency V.cubicAntisymmetricBoxFrequencies) (fun _ : Fin 6 => (N : ℝ))
      (D.filtration.realPolynomialSymbolHom F.basis F.weight F.adapted (fun _ => 1) g) r := by
    have h := F.factorization
    rw [V.cubicAntisymmetricBoxNiltest_symbol] at h
    exact NilpotentLieFiltration.ControlledSymbolFactorization.mono D.filtration
      F.basis F.weight F.adapted h hpr (fun _ => by exact_mod_cast NeZero.pos N)
  obtain ⟨U⟩ := horbit D F.basis F.weight F.adapted hr hgeom (by simpa using h6r)
    (fun i j => (F.height i j).trans hpr) g (piFrequency V.cubicAntisymmetricBoxFrequencies)
    (fun _ : Fin 6 => (N : ℝ)) (fun _ => (Real.exp_le_exp.mpr hfinal).trans hN) hfactor
  exact ⟨U.mono hfinal (fun _ => by exact_mod_cast NeZero.pos N)⟩

end Erdos3

end

end OAI
