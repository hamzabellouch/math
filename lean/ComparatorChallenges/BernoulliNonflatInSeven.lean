import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace Bernoulli
open scoped _root_.Bernoulli

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Compactly supported smooth real tests in the open set. -/
def Test {d : ℕ} (D : Set (Space d)) (φ : Space d → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ D

/-- Distributional gradient, tested in every constant direction. -/
def WeakGradient {d : ℕ} (D : Set (Space d))
    (u : Space d → ℝ) (G : Space d → Space d) : Prop :=
  ∀ φ, Test D φ → ∀ h : Space d,
    (∫ x in D, u x * (fderiv ℝ φ x) h) =
      -(∫ x in D, inner ℝ (G x) h * φ x)

/-- H¹(D), with its weak gradient. -/
def H1 {d : ℕ} (D : Set (Space d))
    (u : Space d → ℝ) (G : Space d → Space d) : Prop :=
  MemLp u 2 (volume.restrict D) ∧
  MemLp G 2 (volume.restrict D) ∧ WeakGradient D u G

/-- H¹₀(D) is H¹-closure of C∞ compactly supported functions.
Both L² errors tend to zero. This does not restrict competitors to smooth ones. -/
def H10 {d : ℕ} (D : Set (Space d))
    (u : Space d → ℝ) (G : Space d → Space d) : Prop :=
  H1 D u G ∧ ∀ ε : ℝ, 0 < ε → ∃ φ : Space d → ℝ,
    Test D φ ∧
    eLpNorm (fun x => u x - φ x) 2 (volume.restrict D) < ENNReal.ofReal ε ∧
    eLpNorm (fun x => G x - gradient φ x) 2 (volume.restrict D) < ENNReal.ofReal ε

/-- Ballwise H¹_loc, on an open set (balls have compact closure inside D). -/
def H1Loc {d : ℕ} (D : Set (Space d))
    (u : Space d → ℝ) (G : Space d → Space d) : Prop :=
  ∀ c : Space d, ∀ r : ℝ, 0 < r → Metric.closedBall c r ⊆ D →
    H1 (Metric.ball c r) u G

/-- The exact volume-one Bernoulli energy, not just Dirichlet energy. -/
def energy {d : ℕ} (D : Set (Space d))
    (u : Space d → ℝ) (G : Space d → Space d) : ℝ :=
  ∫ x in D, ‖G x‖ ^ 2 + if 0 < u x then (1 : ℝ) else 0

/-- Full ballwise local comparison. Competitor and gradient are arbitrary
Sobolev representatives on the ball, with zero-trace difference. -/
def LocalMinimizer {d : ℕ} (D : Set (Space d)) (u : Space d → ℝ) : Prop :=
  IsOpen D ∧ ∃ G : Space d → Space d,
    H1Loc D u G ∧ (∀ᵐ x ∂volume.restrict D, 0 ≤ u x) ∧
    ∀ c : Space d, ∀ r : ℝ, 0 < r → Metric.closedBall c r ⊆ D →
      ∀ (v : Space d → ℝ) (V : Space d → Space d),
        H1 (Metric.ball c r) v V →
        (∀ᵐ x ∂volume.restrict (Metric.ball c r), 0 ≤ v x) →
        H10 (Metric.ball c r) (fun x => v x - u x) (fun x => V x - G x) →
        energy (Metric.ball c r) u G ≤ energy (Metric.ball c r) v V

/-- Nonnegative global minimizer, with all centers and all positive radii. -/
def GlobalMinimizer {d : ℕ} (u : Space d → ℝ) : Prop :=
  LocalMinimizer Set.univ u

def OneHomogeneous {d : ℕ} (u : Space d → ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ᵐ x ∂volume, u (r • x) = r * u x

def Nonzero {d : ℕ} (u : Space d → ℝ) : Prop :=
  ¬ (u =ᵐ[volume] fun _ => 0)

/-- Flatness is a.e. equality of H¹ representatives. -/
def Flat {d : ℕ} (u : Space d → ℝ) : Prop :=
  ∃ e : Space d, ‖e‖ = 1 ∧ ∀ᵐ x ∂volume, u x = max (inner ℝ x e) 0

theorem nonflat_in_seven : ∃ u : Space 7 → ℝ,
    GlobalMinimizer u ∧ Nonzero u ∧ OneHomogeneous u ∧ ¬ Flat u := by
  sorry

end Bernoulli

end

end OAI
