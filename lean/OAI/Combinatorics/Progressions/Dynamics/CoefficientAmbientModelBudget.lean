import OAI.Combinatorics.Progressions.Estimates.NativePhysicalHaarExpansion

namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped BigOperators Classical NNReal

noncomputable def coefficientAmbientModelGeometry (m q : ℕ) : ℕ :=
  Fintype.card (Finset (Fin q)) *
    ((∑ j : Fin m, (boundedBooleanJetRows (Fin q) (j.val + 1)).card) *
      ∑ j : Fin m, Fintype.card (BoundedCoefficientExponent (Fin q) (j.val + 1)))

theorem exists_coefficientAmbientModelTerm_budget (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)]
      (period gridPeriod : ℕ) [NeZero period] [NeZero gridPeriod]
      (g : Finset (Fin q) →
        (((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) ×
          ((Σ j, J j) → UnitAddCircle)) × ((Σ j, J j) → UnitAddCircle)) → ℂ)
      {L : ℝ≥0} {P : ℝ},
      0 ≤ P → (L : ℝ) ≤ Real.exp P → (period : ℝ) ≤ Real.exp P →
      (gridPeriod : ℝ) ≤ Real.exp P →
      (∀ s, LipschitzWith L (g s)) → (∀ s z, ‖g s z‖ ≤ 1) →
      LipschitzWith ⟨Real.exp ((P + A) ^ A), (Real.exp_pos _).le⟩
        (coefficientAmbientModelTerm period gridPeriod g) := by
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget
    ((3 : Polynomial ℕ) * Polynomial.X + Polynomial.C (coefficientAmbientModelGeometry m q))
  refine ⟨A, hA, ?_⟩
  intro J _ period gridPeriod _ _ g L P hP hL hp hg hgL hgb
  apply (coefficientAmbientModelTerm_bounds period gridPeriod g hgL hgb).2.weaken
  apply NNReal.coe_le_coe.mp
  have hpoly : 3 * P + coefficientAmbientModelGeometry m q ≤ (P + A) ^ A := by
    simpa using hbudget P hP
  have hgeom : (coefficientAmbientModelGeometry m q : ℝ) ≤
      Real.exp (coefficientAmbientModelGeometry m q) := by
    linarith [Real.add_one_le_exp (coefficientAmbientModelGeometry m q : ℝ)]
  have hbound : (coefficientAmbientModelGeometry m q : ℝ) * ((L : ℝ) * period * gridPeriod) ≤
      Real.exp (3 * P + coefficientAmbientModelGeometry m q) := by
    calc
      _ ≤ Real.exp (coefficientAmbientModelGeometry m q) *
          (Real.exp P * Real.exp P * Real.exp P) := by gcongr
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have hid : (Fintype.card (Finset (Fin q)) : ℝ) *
      ((L : ℝ) * (period * gridPeriod) *
        ((∑ j : Fin m, ((boundedBooleanJetRows (Fin q) (j.val + 1)).card : ℝ)) *
          ∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin q) (j.val + 1)) : ℝ))) =
      (coefficientAmbientModelGeometry m q : ℝ) * ((L : ℝ) * period * gridPeriod) := by
    simp only [coefficientAmbientModelGeometry, Nat.cast_mul, Nat.cast_sum]
    ring
  have hfinal := hbound.trans (Real.exp_le_exp.mpr hpoly)
  rw [← hid] at hfinal
  simp only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_sum]
  convert hfinal using 1
  congr! (transparency := .reducible)

end Erdos3.BooleanCubeKernel

end

end OAI
