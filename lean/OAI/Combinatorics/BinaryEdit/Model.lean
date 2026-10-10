import OAI.Combinatorics.TreeEdit.Model

namespace OAI
noncomputable section

namespace TreeEdit.BinaryLower

universe u v

/-- The one-sided deficit `r_n`, used on pairs of length `n`. -/
def deficit {α : Type u} (n : ℕ) (x y : List α) : ℕ := n - lcs x y

/-- The usual ℓ₁ distance in finite dimension, not the sup norm on a Pi type. -/
def finiteL1Distance {M : ℕ} (x y : Fin M → ℝ) : ℝ :=
  ∑ i, |x i - y i|

/-- Product of the two maximal ratios. On the finite nontrivial metric spaces
used below each displayed supremum is a maximum. -/
def distortion {X : Type u} (ρ : X → X → ℝ) (f : X → RealL1) : ℝ :=
  sSup {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ‖f x - f y‖ / ρ x y} *
  sSup {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ρ x y / ‖f x - f y‖}

/-- Infimum over every injective map into the full real sequence space ℓ₁;
there is no dimension or computability restriction. -/
def c1 (X : Type u) (ρ : X → X → ℝ) : ℝ :=
  sInf {D : ℝ | ∃ f : X → RealL1, Function.Injective f ∧ D = distortion ρ f}

/-- Words of length at most the specified cap. -/
abbrev WordsLE (α : Type u) (d : ℕ) := {x : List α // x.length ≤ d}

/-- Distortion of the ordinary edit metric on the all-length capped domain. -/
def alphabetDistortion (α : Type u) (d : ℕ) : ℝ :=
  c1 (WordsLE α d) (fun x y => (ed x.val y.val : ℝ))

/-- Distortion of a finite collection of equal-length binary words. -/
def binarySetDistortion {n : ℕ} (W : Finset (Word Bool n)) : ℝ :=
  c1 {x : Word Bool n // x ∈ W}
    (fun x y => (ed x.val.val y.val.val : ℝ))

/-- Supremum over finite alphabets of cardinality at least two, represented by
canonical alphabets `Fin K`. Relabeling invariance identifies this with the
source's supremum over all finite alphabets. -/
def alphabetDistortionSup (d : ℕ) : ℝ :=
  sSup {D : ℝ | ∃ K : ℕ, 2 ≤ K ∧ D = alphabetDistortion (Fin K) d}

/-- Natural-logarithm scale of all three asymptotic endpoints. -/
def growth (c : ℝ) (d : ℕ) : ℝ :=
  Real.exp (c * Real.sqrt (Real.log (d : ℝ) * Real.log (Real.log (d : ℝ))))

end TreeEdit.BinaryLower

end

end OAI
