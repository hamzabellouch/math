import OAI.Geometry.SurfaceImmersion.Correction.PolynomialSolveFactors

namespace OAI

/-!
The size and residual factors depend only on numeric coefficient profiles,
not on the map, phase, chart, target or scale in a solver record.  The pure
profiles let a family use those factors without introducing a reference
solver at unit scale.
-/

noncomputable section

open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

variable {n : ℕ}

def κProfile (P : Fin 3 → Fin n → Expression) (C D : ℕ → ℝ) (m : ℕ) : ℝ :=
  max (SmallModes.errorConstant m (C m))
    (D m * SmallModes.initialConstant 4 (m + tensorOrder P) (C (m + tensorOrder P)))

def sizeProfile (P : Fin 3 → Fin n → Expression) (C D J : ℕ → ℝ) (q m : ℕ) : ℝ :=
  (m.factorial : ℝ) * 2 ^ m *
    SmallModes.forcedModeBudget 4 (tensorOrder P) C D q m * J m ^ m

def residualProfile (P : Fin 3 → Fin n → Expression) (C D J : ℕ → ℝ) (q m : ℕ) : ℝ :=
  tensorChartBudget m (J m) (J (m + 1)) * 2 ^ m *
    FiniteParametrix.boundProfile (tensorOrder P + 1)
      (κProfile P C D) (κProfile P C D) q m

theorem κProfile_nonneg (P : Fin 3 → Fin n → Expression) (C D : ℕ → ℝ)
    (hC : ∀ m, 0 ≤ C m) (m : ℕ) : 0 ≤ κProfile P C D m :=
  (SmallModes.errorConstant_nonneg m (hC m)).trans (le_max_left _ _)

theorem sizeProfile_nonneg (P : Fin 3 → Fin n → Expression) (C D J : ℕ → ℝ)
    (hC : ∀ m, 0 ≤ C m) (hJ : ∀ m, 0 ≤ J m) (q m : ℕ) :
    0 ≤ sizeProfile P C D J q m :=
  mul_nonneg (mul_nonneg (by positivity)
    (SmallModes.forcedModeBudget_nonneg 4 (tensorOrder P) C D hC q m))
    (pow_nonneg (hJ m) _)

theorem residualProfile_nonneg (P : Fin 3 → Fin n → Expression) (C D J : ℕ → ℝ)
    (hC : ∀ m, 0 ≤ C m) (hJ : ∀ m, 0 ≤ J m) (q m : ℕ) :
    0 ≤ residualProfile P C D J q m :=
  mul_nonneg (mul_nonneg (tensorChartBudget_nonneg m (hJ m) (hJ (m + 1))) (by positivity))
    (FiniteParametrix.boundProfile_nonneg (κProfile_nonneg P C D hC)
      (κProfile_nonneg P C D hC) q m)

variable {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : TopologicalSpace.Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

theorem κ_eq_κProfile {C D : ℕ → ℝ} (hC : c.C = C) (hD : c.D = D) :
    c.κ = κProfile P C D := by
  funext m
  simp only [κ, κProfile, hC, hD]

theorem sizeFactor_eq_sizeProfile {C D J : ℕ → ℝ}
    (hC : c.C = C) (hD : c.D = D) (hJ : c.J = J) (q m : ℕ) :
    c.sizeFactor q m = sizeProfile P C D J q m := by
  simp only [sizeFactor, sizeProfile, hC, hD, hJ]

theorem residualFactor_eq_residualProfile {C D J : ℕ → ℝ}
    (hC : c.C = C) (hD : c.D = D) (hJ : c.J = J) (q m : ℕ) :
    c.residualFactor q m = residualProfile P C D J q m := by
  simp only [residualFactor, residualProfile, hJ, c.κ_eq_κProfile hC hD]

/-- Solver records at different maps or scales have the same factors when
their three numeric profiles agree. -/
theorem factors_eq_of_profiles
    {ε' τ' : ℝ} {H : Base → Space} {hH : ContDiff ℝ ∞ H} {ψ : Base → ℝ}
    {L : TopologicalSpace.Compacts Base} {s' : ℝ≥0}
    (d : PolynomialSolveData P ε' H hH ψ L τ' s')
    (hC : c.C = d.C) (hD : c.D = d.D) (hJ : c.J = d.J) (q m : ℕ) :
    c.sizeFactor q m = d.sizeFactor q m ∧
      c.residualFactor q m = d.residualFactor q m := by
  constructor
  · exact (c.sizeFactor_eq_sizeProfile hC hD hJ q m).trans
      (d.sizeFactor_eq_sizeProfile rfl rfl rfl q m).symm
  · exact (c.residualFactor_eq_residualProfile hC hD hJ q m).trans
      (d.residualFactor_eq_residualProfile rfl rfl rfl q m).symm

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
