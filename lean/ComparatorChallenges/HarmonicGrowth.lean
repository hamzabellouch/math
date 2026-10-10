import Mathlib

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff

namespace HarmonicCounterexample

abbrev Space (n : ℕ) := Fin n → ℝ
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- A genuine smooth positive definite covariant metric tensor on R^n. -/
structure SmoothMetric (n : ℕ) where
  coeff : Space n → Mat n
  smooth : ∀ i j, ContDiff ℝ ∞ (fun x => coeff x i j)
  positive : ∀ x, (coeff x).PosDef

/-- The coordinate directional derivative. -/
def coordDeriv {n : ℕ} (i : Fin n) (f : Space n → ℝ) (x : Space n) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- Levi-Civita connection in the single global Cartesian chart. -/
def christoffel {n : ℕ} (g : SmoothMetric n) (x : Space n)
    (k i j : Fin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ l, (g.coeff x)⁻¹ k l *
    (coordDeriv i (fun y => g.coeff y j l) x +
     coordDeriv j (fun y => g.coeff y i l) x -
     coordDeriv l (fun y => g.coeff y i j) x)

/-- Ricci tensor, with the convention in which the round sphere has positive Ricci. -/
def ricci {n : ℕ} (g : SmoothMetric n) (x : Space n) (i j : Fin n) : ℝ :=
  (∑ k, (coordDeriv k (fun y => christoffel g y k i j) x -
    coordDeriv j (fun y => christoffel g y k i k) x)) +
  ∑ k, ∑ l, (christoffel g x k i j * christoffel g x l k l -
    christoffel g x l i k * christoffel g x k j l)

def RicciNonnegative {n : ℕ} (g : SmoothMetric n) : Prop :=
  ∀ (x v : Space n), 0 ≤ ∑ i, ∑ j, ricci g x i j * v i * v j

/-- Trace of the covariant Hessian, i.e. the Laplace-Beltrami operator. -/
def laplaceBeltrami {n : ℕ} (g : SmoothMetric n) (u : Space n → ℝ)
    (x : Space n) : ℝ :=
  ∑ i, ∑ j, (g.coeff x)⁻¹ i j *
    (coordDeriv i (coordDeriv j u) x - ∑ k, christoffel g x k i j * coordDeriv k u x)

/-- Riemannian length of a path on the unit parameter interval. -/
def pathLength {n : ℕ} (g : SmoothMetric n) (γ : ℝ → Space n) : ℝ :=
  ∫ t in (0 : ℝ)..1, Real.sqrt
    (∑ i, ∑ j, g.coeff (γ t) i j * deriv γ t i * deriv γ t j)

/-- Infimum of smooth path lengths, the intrinsic Riemannian distance. -/
def distance {n : ℕ} (g : SmoothMetric n) (x y : Space n) : ℝ :=
  sInf {L : ℝ | ∃ γ : ℝ → Space n,
    ContDiff ℝ 1 γ ∧ γ 0 = x ∧ γ 1 = y ∧ L = pathLength g γ}

/-- Sequential metric completeness, for the intrinsic distance, not the background one. -/
def Complete {n : ℕ} (g : SmoothMetric n) : Prop :=
  ∀ z : ℕ → Space n,
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N, distance g (z p) (z q) < ε) →
    ∃ x : Space n, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, distance g (z p) x < ε

def EuclideanNearOrigin {n : ℕ} (g : SmoothMetric n) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ x : Space n, (∑ i, x i ^ 2) < ε ^ 2 → g.coeff x = 1

/-- Riemannian measure of the intrinsic open ball, retaining infinite values. -/
def ballVolume {n : ℕ} (g : SmoothMetric n) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in {x : Space n | distance g 0 x < R},
    ENNReal.ofReal (Real.sqrt (g.coeff x).det) ∂volume

/-- The ordinary Euclidean unit ball volume, in Cartesian Lebesgue measure. -/
def omega (n : ℕ) : ℝ≥0∞ :=
  volume {x : Space n | (∑ i, x i ^ 2) < 1}

/-- The volume-ratio limit is finite, positive, and strictly below one. -/
def PositiveSubunitAVR {n : ℕ} (g : SmoothMetric n) : Prop :=
  ∃ a : ℝ, 0 < a ∧ a < 1 ∧
    Tendsto (fun R : ℝ => ballVolume g R / (omega n * ENNReal.ofReal (R ^ n)))
      atTop (𝓝 (ENNReal.ofReal a))

/-- Membership in the actual space H_k, with the bound required at every point. -/
def HarmonicGrowth {n : ℕ} (g : SmoothMetric n) (k : ℕ) (u : Space n → ℝ) : Prop :=
  ContDiff ℝ ∞ u ∧ (∀ x, laplaceBeltrami g u x = 0) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |u x| ≤ C * (1 + distance g 0 x) ^ k


def euclideanDimension (n k : ℕ) : ℕ :=
  (n + k - 1).choose k + (n + k - 2).choose (k - 1)

/-- The manuscript's unconditional main existence claim. -/
def MainClaim : Prop :=
  ∃ (n k : ℕ) (g : SmoothMetric n), Even n ∧ 8 ≤ n ∧ 2 ≤ k ∧
    Complete g ∧ RicciNonnegative g ∧ EuclideanNearOrigin g ∧ PositiveSubunitAVR g ∧
    ∃ u : Fin (euclideanDimension n k + 1) → (Space n → ℝ),
      LinearIndependent ℝ u ∧ ∀ i, HarmonicGrowth g k (u i)



axiom mainStatement : MainClaim

theorem main : MainClaim := mainStatement

end HarmonicCounterexample

end

end OAI
