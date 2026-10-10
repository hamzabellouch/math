import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe uX u_1

namespace ExactModuli

variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Closed linear subspaces of finite codimension. -/
def Cofinite (F : Submodule ℝ X) : Prop :=
  IsClosed (F : Set X) ∧ FiniteDimensional ℝ (X ⧸ F)

/-- Averaged increment for directions of norm at least one. -/
def averagedIncrement (N : Seminorm ℝ X) (x : X) (t : ℝ) (y : X) : ℝ :=
  (N (x + t • y) + N (x - t • y)) / 2 - 1

def H (N : Seminorm ℝ X) (x : X) (t : ℝ) : ℝ :=
  sSup {r | ∃ F : Submodule ℝ X, Cofinite F ∧
    r = sInf {a | ∃ y ∈ F, 1 ≤ N y ∧ a = averagedIncrement N x t y}}

def D (N : Seminorm ℝ X) (x : X) (t : ℝ) : ℝ :=
  sSup {r | ∃ F : Submodule ℝ X, Cofinite F ∧
    r = sInf {a | ∃ y ∈ F, N y = 1 ∧ a = N (x + t • y) - 1}}

def averagedModulus (N : Seminorm ℝ X) (t : ℝ) : ℝ :=
  sInf {r | ∃ x, N x = 1 ∧ r = H N x t}

def oneSidedModulus (N : Seminorm ℝ X) (t : ℝ) : ℝ :=
  sInf {r | ∃ x, N x = 1 ∧ r = D N x t}

/-- Two-sided comparison makes this seminorm a genuine norm equivalent to the original. -/
def EquivalentNorm (N : Seminorm ℝ X) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ x, a * ‖x‖ ≤ N x ∧ N x ≤ b * ‖x‖

def AUC (N : Seminorm ℝ X) : Prop :=
  ∀ t : ℝ, 0 < t → 0 < oneSidedModulus N t

/-- Every rank-one operator has the form `ell.smulRight v`. -/
def Daugavet (X : Type uX) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∀ (ell : X →L[ℝ] ℝ) (v : X),
    ‖ContinuousLinearMap.id ℝ X + ell.smulRight v‖ = 1 + ‖ell.smulRight v‖

variable {Ω : Type u_1} [MeasurableSpace Ω] (μ : Measure Ω)

/-- Convergence-in-measure distance on L1 equivalence classes. -/
def measureDistance (f g : Lp ℝ 1 μ) : ℝ :=
  sInf {a : ℝ | 0 < a ∧ μ.real {ω | a < |f ω - g ω|} < a}

/-- Finite covers of the entire unit ball in convergence-in-measure distance. -/
def MeasurePrecompactBall (E : Submodule ℝ (Lp ℝ 1 μ)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ s : Finset (Lp ℝ 1 μ),
    ∀ y : E, ‖y‖ ≤ 1 → ∃ b ∈ s, measureDistance μ (y : Lp ℝ 1 μ) b < ε

/-- Every nonempty unit-ball slice contains an almost antipodal unit vector. -/
def UnitSliceProperty (X : Type uX) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∀ (w : X), ‖w‖ = 1 → ∀ (ell : X →L[ℝ] ℝ) (α : ℝ),
    (∃ u : X, ‖u‖ ≤ 1 ∧ α < ell u) →
    ∀ ρ : ℝ, 0 < ρ → ∃ y : X, ‖y‖ = 1 ∧ α < ell y ∧ 2 - ρ ≤ ‖w + y‖

/-- The countable product of unit intervals. -/
abbrev KWOmega := ℕ → unitInterval

def kwMeasure : Measure KWOmega := Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval))

theorem exact_main {Ω : Type u_1} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (E : Submodule ℝ (Lp ℝ 1 μ))
    (_hclosed : IsClosed (E : Set (Lp ℝ 1 μ))) (hdim : ¬ FiniteDimensional ℝ E)
    (hprecompact : MeasurePrecompactBall μ E) (hdaugavet : Daugavet E) :
    (∀ (x : E), ‖x‖ = 1 → ∀ t : ℝ, 0 < t →
      H (normSeminorm ℝ E) x t = max (t / 2) (t - 1) ∧
      D (normSeminorm ℝ E) x t = max 0 (t - 2)) ∧
    (∀ t : ℝ, 0 < t →
      averagedModulus (normSeminorm ℝ E) t = max (t / 2) (t - 1) ∧
      oneSidedModulus (normSeminorm ℝ E) t = max 0 (t - 2)) ∧
    (∀ N : Seminorm ℝ E, EquivalentNorm N → ¬ AUC N) := by
  sorry

theorem kadets_werner_existence :
    ∃ E : Submodule ℝ (Lp ℝ 1 kwMeasure),
      IsClosed (E : Set (Lp ℝ 1 kwMeasure)) ∧ (¬ FiniteDimensional ℝ E) ∧
      MeasurePrecompactBall kwMeasure E ∧ UnitSliceProperty E ∧ Daugavet E := by
  sorry

theorem exact_example :
    ∃ E : Submodule ℝ (Lp ℝ 1 kwMeasure),
      IsClosed (E : Set (Lp ℝ 1 kwMeasure)) ∧ (¬ FiniteDimensional ℝ E) ∧
      MeasurePrecompactBall kwMeasure E ∧ UnitSliceProperty E ∧ Daugavet E ∧
      (∀ (x : E), ‖x‖ = 1 → ∀ t : ℝ, 0 < t →
        H (normSeminorm ℝ E) x t = max (t / 2) (t - 1) ∧
        D (normSeminorm ℝ E) x t = max 0 (t - 2)) ∧
      (∀ t : ℝ, 0 < t →
        averagedModulus (normSeminorm ℝ E) t = max (t / 2) (t - 1) ∧
        oneSidedModulus (normSeminorm ℝ E) t = max 0 (t - 2)) ∧
      (∀ N : Seminorm ℝ E, EquivalentNorm N → ¬ AUC N) := by
  sorry

end ExactModuli

end

end OAI
