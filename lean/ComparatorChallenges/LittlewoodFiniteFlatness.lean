import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter Complex
open scoped BigOperators Topology ComplexConjugate

namespace AsymptoticallyMinimalLittlewoodFiniteFlatness

/-- The consecutive-degree polynomial of a real coefficient family. -/
def littlewoodValue {N : ℕ} (ε : Fin N → ℝ) (z : ℂ) : ℂ :=
  ∑ k : Fin N, (ε k : ℂ) * z ^ (k : ℕ)

/-- Every coefficient is a real sign. -/
def IsRealSigning {N : ℕ} (ε : Fin N → ℝ) : Prop :=
  ∀ k, ε k = -1 ∨ ε k = 1

def MainStatement : Prop :=
  ∃ ε : (N : ℕ) → Fin N → ℝ,
    (∀ N : ℕ, IsRealSigning (ε N)) ∧
    ∀ p : ℝ, 0 < p →
      Filter.Tendsto
        (fun N : ℕ =>
          ∫ t : UnitAddCircle,
            Real.rpow
              |‖littlewoodValue (ε N) (fourier (1 : ℤ) t)‖ /
                  Real.sqrt (N : ℝ) - 1|
              p
            ∂AddCircle.haarAddCircle)
        Filter.atTop (𝓝 (0 : ℝ))

/-- One all-length real-sign family for every finite positive real exponent. -/
theorem main : MainStatement := by
  sorry

end AsymptoticallyMinimalLittlewoodFiniteFlatness

end

end OAI
