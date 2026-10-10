import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

namespace AffineBernstein

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def coordinateVector (n : ℕ) (i : Fin n) : Space n :=
  EuclideanSpace.single i 1

/-- Coordinate Hessian. On the open domain it depends only on the restriction of `u`.
The order of the two differentiations is immaterial under the smoothness hypothesis. -/
def hessian {n : ℕ} (u : Space n → ℝ) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => fderiv ℝ (fun y => fderiv ℝ u y (coordinateVector n j)) x
    (coordinateVector n i)

/-- The coefficient U^{ij} = det(D²u) (D²u)^{-1}_{ij}. -/
def cofactorHessian {n : ℕ} (u : Space n → ℝ) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ :=
  (hessian u x).det • (hessian u x)⁻¹

/-- The classical determinant weight; in particular, this is not a generalized exponent. -/
def affineWeight {n : ℕ} (u : Space n → ℝ) (x : Space n) : ℝ :=
  Real.rpow (hessian u x).det (-(((n : ℝ) + 1) / ((n : ℝ) + 2)))

def AffineMaximalOn {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ) : Prop :=
  ∀ x ∈ Ω, ∑ i : Fin n, ∑ j : Fin n,
    cofactorHessian u x i j * hessian (affineWeight u) x i j = 0

/-- Length on [0,1] for g_x(v,v) = ‖v‖² + (Du_x v)², the metric induced
by the Euclidean graph embedding x ↦ (x,u(x)). The product norm on Lean's ordinary
product type is NOT used (it would be the maximum norm). -/
def graphPathLength {n : ℕ} (u : Space n → ℝ) (γ : ℝ → Space n) : ℝ≥0∞ :=
  ∫⁻ t in Icc (0 : ℝ) 1,
    ENNReal.ofReal (Real.sqrt
      (‖derivWithin γ (Icc (0 : ℝ) 1) t‖ ^ 2 +
       (fderiv ℝ u (γ t) (derivWithin γ (Icc (0 : ℝ) 1) t)) ^ 2))

/-- The intrinsic extended distance: infimum of lengths of C¹ paths in the domain.
Using a single C¹ path gives the same intrinsic distance as piecewise C¹ paths,
by smooth endpoint reparameterization and concatenation. -/
def graphEDist {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (x y : Space n) : ℝ≥0∞ :=
  ⨅ (γ : ℝ → Space n)
    (_ : ContDiffOn ℝ 1 γ (Icc (0 : ℝ) 1))
    (_ : MapsTo γ (Icc (0 : ℝ) 1) Ω)
    (_ : γ 0 = x) (_ : γ 1 = y), graphPathLength u γ

/-- Sequential completeness for the induced Euclidean path metric. This states
that every intrinsic Cauchy sequence of points in Ω has an intrinsic limit in Ω.
It imposes no growth condition and no completeness condition on the affine metric. -/
def EuclideanGraphComplete {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ) : Prop :=
  ∀ x : ℕ → Space n, (∀ i, x i ∈ Ω) →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      graphEDist Ω u (x i) (x j) < ENNReal.ofReal ε) →
    ∃ a ∈ Ω, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i ≥ N,
      graphEDist Ω u (x i) a < ENNReal.ofReal ε

/-- The graph, regarded as an affine subset of R^{n+1}. -/
def graph {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ) : Set (Space n × ℝ) :=
  {p | p.1 ∈ Ω ∧ p.2 = u p.1}

def standardParaboloid (n : ℕ) : Set (Space n × ℝ) :=
  {p | p.2 = ∑ i : Fin n, (p.1 i) ^ 2}

/-- Literal main theorem, with its stated affine-image consequence. -/
theorem affine_bernstein
    (n : ℕ) (hn₃ : 3 ≤ n) (hn₉ : n ≤ 9)
    (Ω : Set (Space n)) (hΩne : Ω.Nonempty) (hΩopen : IsOpen Ω)
    (hΩconvex : Convex ℝ Ω) (u : Space n → ℝ)
    (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hmax : AffineMaximalOn Ω u)
    (hcomplete : EuclideanGraphComplete Ω u) :
    Ω = univ ∧
      (∃ (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) (c : ℝ),
        A.IsSymm ∧ A.PosDef ∧
        ∀ x, u x = (1 / 2 : ℝ) * (∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j)
          + (∑ i : Fin n, b i * x i) + c) ∧
      (∃ e : (Space n × ℝ) ≃ᵃ[ℝ] (Space n × ℝ),
        e '' standardParaboloid n = graph Ω u) := by
  sorry

end AffineBernstein

end

end OAI
