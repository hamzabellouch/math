import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uX

namespace IndependentProducts

/-- The tree of finite sequences of positive integers. -/
abbrev Vertex := List ℕ+
/-- Coordinates are attached only to nonroot vertices. -/
abbrev Edge := {v : Vertex // v ≠ []}
abbrev Sample := Edge → ℝ

/-- The product law of independent copies of the multiplier. -/
def productMeasure (μ : Measure ℝ) : Measure Sample :=
  Measure.infinitePi (fun _ : Edge => μ)

/-- The nonroot prefix ending at position `j`. -/
def pathPrefix (v : Vertex) (j : Fin v.length) : Edge :=
  ⟨v.take (j.val + 1), by
    intro h
    have hl := congrArg List.length h
    simp only [List.length_take, List.length_nil] at hl
    have := j.isLt
    omega⟩

/-- Root product is the empty product 1; every other product uses the path prefixes. -/
def pathProduct (v : Vertex) (ω : Sample) : ℝ :=
  ∏ j : Fin v.length, ω (pathPrefix v j)

/-- The closed real L1 span of the path products. -/
def productSpan (μ : Measure ℝ) : Submodule ℝ (Lp ℝ 1 (productMeasure μ)) :=
  (Submodule.span ℝ {f : Lp ℝ 1 (productMeasure μ) | ∃ v : Vertex,
    (f : Sample → ℝ) =ᵐ[productMeasure μ] pathProduct v}).topologicalClosure

/-- Positivity, nonconstancy, mean one, and finite second moment of the multiplier law. -/
structure MultiplierHypotheses (μ : Measure ℝ) : Prop where
  probability : IsProbabilityMeasure μ
  positive : ∀ᵐ w ∂μ, 0 < w
  nonconstant : ∀ c : ℝ, ¬ (∀ᵐ w ∂μ, w = c)
  mean_one : ∫ w, w ∂μ = 1
  second_moment : MemLp (fun w : ℝ => w) 2 μ

section Moduli

variable (X : Type uX) [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Closed subspaces of finite codimension, with respect to the inherited topology. -/
def CofiniteSubspaces : Set (Submodule ℝ X) :=
  {F | IsClosed (F : Set X) ∧ FiniteDimensional ℝ (X ⧸ F)}

/-- The averaged asymptotic midpoint modulus, with directions of norm at least 1. -/
def averagedMidpointModulus (N : Seminorm ℝ X) (t : ℝ) : ℝ :=
  sInf {r | ∃ x : X, N x = 1 ∧ r =
    sSup {a | ∃ F ∈ CofiniteSubspaces X, a =
      sInf {b | ∃ y : X, y ∈ F ∧ 1 ≤ N y ∧
        b = (N (x + t • y) + N (x - t • y)) / 2 - 1}}}

/-- The usual one-sided modulus, whose directions have norm exactly 1. -/
def oneSidedModulus (N : Seminorm ℝ X) (t : ℝ) : ℝ :=
  sInf {r | ∃ x : X, N x = 1 ∧ r =
    sSup {a | ∃ F ∈ CofiniteSubspaces X, a =
      sInf {b | ∃ y : X, y ∈ F ∧ N y = 1 ∧ b = N (x + t • y) - 1}}}

/-- A seminorm with these bounds is a genuine norm equivalent to the original norm. -/
def IsEquivalentNorm (N : Seminorm ℝ X) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ x, a * ‖x‖ ≤ N x ∧ N x ≤ b * ‖x‖

def IsAUC (N : Seminorm ℝ X) : Prop := ∀ t : ℝ, 0 < t → 0 < oneSidedModulus X N t

end Moduli

/-- Gaussian-tail probability, in real rather than extended-nonnegative-real notation. -/
def gaussianTail (r : ℝ) : ℝ :=
  (gaussianReal 0 1 {x : ℝ | r ≤ |x|}).toReal

/-- The Gaussian excess constant at threshold twice the parameter. -/
def excessConstant (K : ℝ) : ℝ :=
  (1 / 16 : ℝ) * ∫ x : ℝ, max (|x| - 2 * K) 0 ∂gaussianReal 0 1

/-- The density exp(-w) on the positive half-line. -/
def exponentialLaw : Measure ℝ := expMeasure 1

/-- The law of the square of a standard real Gaussian. -/
def gaussianSquareLaw : Measure ℝ := (gaussianReal 0 1).map (fun x : ℝ => x ^ 2)

end IndependentProducts

end

end OAI
