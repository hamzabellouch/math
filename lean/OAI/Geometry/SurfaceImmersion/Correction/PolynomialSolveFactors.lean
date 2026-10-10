import OAI.Geometry.SurfaceImmersion.Correction.PolynomialSolveData
import OAI.Geometry.SurfaceImmersion.Primitive.FiniteProfileBounds

namespace OAI

/-! Separate the finite input norm and the small residual power from the
geometric solver constants. The input order is explicit. -/
noncomputable section
open scoped NNReal ContDiff
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : TopologicalSpace.Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

def inputOrder (q m : ℕ) : ℕ := m + (q + 1) * (tensorOrder P + 1)

def sizeFactor (q m : ℕ) : ℝ :=
  (m.factorial : ℝ) * 2 ^ m * SmallModes.forcedModeBudget 4 (tensorOrder P) c.C c.D q m * c.J m ^ m

def residualFactor (q m : ℕ) : ℝ :=
  tensorChartBudget m (c.J m) (c.J (m + 1)) * 2 ^ m *
    FiniteParametrix.boundProfile (tensorOrder P + 1) c.κ c.κ q m

lemma sizeFactor_nonneg (q m : ℕ) : 0 ≤ c.sizeFactor q m := by
  have hj : 0 ≤ c.J m := zero_le_one.trans (c.oneLEJ m)
  exact mul_nonneg (mul_nonneg (by positivity)
    (SmallModes.forcedModeBudget_nonneg 4 (tensorOrder P) c.C c.D c.nonnegC q m)) (pow_nonneg hj _)

lemma κ_nonneg (m : ℕ) : 0 ≤ c.κ m :=
  (SmallModes.errorConstant_nonneg m (c.nonnegC m)).trans (le_max_left _ _)

lemma residualFactor_nonneg (q m : ℕ) : 0 ≤ c.residualFactor q m := by
  exact mul_nonneg (mul_nonneg (tensorChartBudget_nonneg m
    (zero_le_one.trans (c.oneLEJ m)) (zero_le_one.trans (c.oneLEJ (m + 1)))) (by positivity))
    (FiniteParametrix.boundProfile_nonneg c.κ_nonneg c.κ_nonneg q m)

lemma size_eq_factor (f : SupportedField (F := PhaseMean.ComplexTensor) (modeSupport K)) (q m : ℕ) :
    c.size f q m = c.sizeFactor q m * c.norm f (inputOrder (P := P) q m) := by
  unfold size sizeFactor inputOrder
  ring

lemma residual_eq_factor (f : SupportedField (F := PhaseMean.ComplexTensor) (modeSupport K)) (q m : ℕ) :
    c.residual f q m = (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) *
      c.residualFactor q m * c.norm f (inputOrder (P := P) q m) := by
  unfold residual residualFactor inputOrder
  rw [FiniteParametrix.boundProfile_terminal]
  ring

lemma size_le_scaled {a A : ℝ} (_ha : 0 ≤ a)
    (f : SupportedField (F := PhaseMean.ComplexTensor) (modeSupport K)) (q m : ℕ)
    (hb : c.norm f (inputOrder (P := P) q m) ≤ a * A) :
    c.size f q m ≤ a * (c.sizeFactor q m * A) := by
  rw [c.size_eq_factor]
  calc
    _ ≤ c.sizeFactor q m * (a * A) := mul_le_mul_of_nonneg_left hb (c.sizeFactor_nonneg q m)
    _ = _ := by ring

lemma residual_le_scaled {a A : ℝ} (hη : 0 ≤ τ / s + ε / τ ^ tensorLoss P)
    (f : SupportedField (F := PhaseMean.ComplexTensor) (modeSupport K)) (q m : ℕ)
    (hb : c.norm f (inputOrder (P := P) q m) ≤ a * A) :
    c.residual f q m ≤ a * (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) * (c.residualFactor q m * A) := by
  rw [c.residual_eq_factor]
  calc
    _ ≤ (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) * c.residualFactor q m * (a * A) :=
      mul_le_mul_of_nonneg_left hb (mul_nonneg (pow_nonneg hη _) (c.residualFactor_nonneg q m))
    _ = _ := by ring

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
