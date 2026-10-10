import OAI.Analysis.KadisonSimilarity.Tracial.ConcreteHalfProjection
import OAI.Analysis.KadisonSimilarity.Tracial.TracialMatrixTower
import OAI.Analysis.FactorGeneration.PartialUnitaries

namespace OAI

/-! The dyadic signs in a diffuse finite tracial von Neumann algebra form
the real tracial sequence required by the matrix-tower construction. The
underlying projections have compatible dyadic refinements and
orthogonality relations. -/

noncomputable section
namespace KadisonSimilarity

open UltrapowerBridge Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- The two existing bundles contain the same vector trace. -/
theorem concreteTraceLinear_eq_coordinateTraceLinear (τ : TracialRepresentation M) :
    concreteTraceLinear τ = coordinateTraceLinear τ := by
  ext a
  rfl

variable (τ : TracialRepresentation M)
  (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)

/-- The successive dyadic signs, based at the identity projection. -/
def concreteRademacher (n : ℕ) : M.toStarSubalgebra :=
  dyadicRademacher τ hdiff ⟨1, IsStarProjection.one _⟩ n

@[simp] theorem concreteRademacher_star (n : ℕ) :
    star (concreteRademacher τ hdiff n) = concreteRademacher τ hdiff n :=
  dyadicRademacher_star τ hdiff ⟨1, IsStarProjection.one _⟩ n

@[simp] theorem concreteRademacher_square (n : ℕ) :
    concreteRademacher τ hdiff n * concreteRademacher τ hdiff n = 1 :=
  dyadicRademacher_sq τ hdiff ⟨1, IsStarProjection.one _⟩ n

theorem concreteRademacher_trace (n : ℕ) :
    concreteTraceLinear τ (concreteRademacher τ hdiff n) = 0 := by
  change τ.trace (dyadicRademacher τ hdiff ⟨1, IsStarProjection.one _⟩ n) = 0
  have h := dyadicRademacher_centered_over_previous τ hdiff
    ⟨1, IsStarProjection.one _⟩ n (fun _ => 1)
  rw [dyadicEval_one τ hdiff ⟨1, IsStarProjection.one _⟩ n] at h
  simpa only [one_mul] using h

/-- Refining earlier signs to the next finite dyadic algebra proves the
off-diagonal moments; the diagonal follows from the square identity. -/
theorem concreteRademacher_inner (i j : ℕ) :
    concreteTraceLinear τ
      (star (concreteRademacher τ hdiff i) * concreteRademacher τ hdiff j) =
      if i = j then 1 else 0 := by
  rw [concreteRademacher_star]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, concreteRademacher_square, concreteTraceLinear_one]
  · rw [ite_eq_right hij]
    exact dyadicRademacher_trace_mul_of_ne τ hdiff ⟨1, IsStarProjection.one _⟩ hij

/-- A concrete diffuse tracial von Neumann algebra supplies the full real
sequence without an independent orthonormal-sequence existence premise. -/
def concreteRealTracialSequence : RealTracialSequence (concreteTraceLinear τ) where
  vector := concreteRademacher τ hdiff
  trace_zero := concreteRademacher_trace τ hdiff
  selfadjoint := concreteRademacher_star τ hdiff
  inner := concreteRademacher_inner τ hdiff

end KadisonSimilarity

end

end OAI
