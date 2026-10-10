import Mathlib

namespace OAI

noncomputable section

namespace QuadricCounterexample

open Set Filter Topology Metric OnePoint

open scoped Matrix.Norms.Elementwise ComplexOrder

abbrev ProjectiveLine := OnePoint ℂ
abbrev QuadricSurface := ProjectiveLine × ProjectiveLine

def reciprocalP1 (x : ProjectiveLine) : ProjectiveLine :=
  x.elim (0 : ℂ) (fun z ↦ if z = 0 then ∞ else (z⁻¹ : ℂ))

def affineP1 (i : Fin 2) (z : ℂ) : ProjectiveLine :=
  if i = 0 then reciprocalP1 z else (z : ProjectiveLine)

def affineQuadric (i : Fin 2 × Fin 2) (z : ℂ × ℂ) : QuadricSurface :=
  (affineP1 i.1 z.1, affineP1 i.2 z.2)

def coordP1 (i : Fin 2) (x : ProjectiveLine) : ℂ :=
  (if i=0 then reciprocalP1 x else x).elim 0 id
def coordQuadric (i : Fin 2 × Fin 2) (x : QuadricSurface) : ℂ × ℂ :=
  (coordP1 i.1 x.1,coordP1 i.2 x.2)

def powerP1 (m : ℕ) (x : ProjectiveLine) : ProjectiveLine :=
  x.elim ∞ (fun z ↦ ((z^m : ℂ) : ProjectiveLine))
def powerQuadric (m : ℕ) (x : QuadricSurface) : QuadricSurface :=
  (powerP1 m x.1,powerP1 m x.2)

abbrev BaseCoordinates := ℂ × ℂ
abbrev FiberCoordinates := Fin 2 → ℂ
abbrev TwoMatrix := Matrix (Fin 2) (Fin 2) ℂ
abbrev BasePolynomial := MvPolynomial (Fin 2) ℂ
def baseEval (p : BasePolynomial) (z : BaseCoordinates) : ℂ :=
  MvPolynomial.eval ![z.1,z.2] p

def AlgebraicallyRegularOn (U : Set BaseCoordinates) (f : BaseCoordinates → ℂ) : Prop :=
  ∀ z ∈ U, ∃ p q : BasePolynomial, baseEval q z ≠ 0 ∧
    ∀ w ∈ U, baseEval q w ≠ 0 → f w=baseEval p w/baseEval q w

def principalChart (i : Fin 2 × Fin 2) (p : BasePolynomial) : Set QuadricSurface :=
  {x | x ∈ range (affineQuadric i) ∧ baseEval p (coordQuadric i x) ≠ 0}

structure AlgebraicRankTwoBundle where
  numberOfCharts : ℕ
  chart : ℕ → Fin 2 × Fin 2
  equation : ℕ → BasePolynomial
  finiteCover : ∀ i, numberOfCharts ≤ i → equation i=0
  covers : ∀ x : QuadricSurface, ∃ i, x ∈ principalChart (chart i) (equation i)
  transition : ℕ → ℕ → QuadricSurface → TwoMatrix
  transition_self : ∀ i x, x ∈ principalChart (chart i) (equation i) →
    transition i i x=1
  transition_mul : ∀ i j k x,
    x ∈ principalChart (chart i) (equation i) →
    x ∈ principalChart (chart j) (equation j) →
    x ∈ principalChart (chart k) (equation k) →
    transition i j x * transition j k x=transition i k x
  transition_regular : ∀ i j a b, AlgebraicallyRegularOn
    {z | baseEval (equation i) z ≠ 0 ∧
      affineQuadric (chart i) z ∈ principalChart (chart j) (equation j)}
    (fun z ↦ transition i j (affineQuadric (chart i) z) a b)

namespace AlgebraicRankTwoBundle

def domain (V : AlgebraicRankTwoBundle) (i : ℕ) : Set QuadricSurface :=
  principalChart (V.chart i) (V.equation i)
def coordinateDomain (V : AlgebraicRankTwoBundle) (i : ℕ) : Set BaseCoordinates :=
  {z | baseEval (V.equation i) z ≠ 0}

def dualTransition (V : AlgebraicRankTwoBundle) (i j : ℕ) (x : QuadricSurface) : TwoMatrix :=
  (V.transition j i x).transpose

end AlgebraicRankTwoBundle

def hyperplaneTransition (i j : Fin 2) (x : ProjectiveLine) : ℂ :=
  if i=j then 1 else coordP1 i x
def polarizationTransition (i j : Fin 2 × Fin 2) (x : QuadricSurface) : ℂ :=
  hyperplaneTransition i.1 j.1 x.1 * hyperplaneTransition i.2 j.2 x.2

def IsPowerPullbackTwist (G : AlgebraicRankTwoBundle) (m : ℕ)
    (E : AlgebraicRankTwoBundle) : Prop :=
  E.numberOfCharts=G.numberOfCharts ∧ E.chart=G.chart ∧
  (∀ i, E.equation i = (MvPolynomial.bind₁ fun j ↦ MvPolynomial.X j ^ m) (G.equation i)) ∧
  ∀ i j x, x ∈ E.domain i → x ∈ E.domain j →
    E.transition i j x = polarizationTransition (G.chart i) (G.chart j) x •
      G.transition i j (powerQuadric m x)

structure SymmetricSection (V : AlgebraicRankTwoBundle) (n : ℕ) where
  coefficient : ℕ → Fin (n+1) → BaseCoordinates → ℂ
  regular : ∀ i k, AlgebraicallyRegularOn (V.coordinateDomain i) (coefficient i k)
  compatible : ∀ i j x, x ∈ V.domain i → x ∈ V.domain j → ∀ v : FiberCoordinates,
    (∑ k : Fin (n+1), coefficient i k (coordQuadric (V.chart i) x) *
      ((V.dualTransition i j x).mulVec v 0)^k.val *
      ((V.dualTransition i j x).mulVec v 1)^(n-k.val)) =
    ∑ k : Fin (n+1), coefficient j k (coordQuadric (V.chart j) x) * v 0^k.val * v 1^(n-k.val)

def SymmetricSection.value {V : AlgebraicRankTwoBundle} {n : ℕ}
    (s : SymmetricSection V n) (i : ℕ) (x : QuadricSurface) (v : FiberCoordinates) : ℂ :=
  ∑ k : Fin (n+1), s.coefficient i k (coordQuadric (V.chart i) x) * v 0^k.val * v 1^(n-k.val)

def ProjectiveAlgebraicCone {N : ℕ} (C : Set (Fin N → ℂ)) : Prop :=
  ∃ equations : Set (MvPolynomial (Fin N) ℂ),
    (∀ p ∈ equations, ∃ d : ℕ, p.IsHomogeneous d) ∧
    C = {y | ∀ p ∈ equations, MvPolynomial.eval y p=0}

def sectionVector {V : AlgebraicRankTwoBundle} {n N : ℕ}
    (s : Fin N → SymmetricSection V n) (i : ℕ) (x : QuadricSurface)
    (v : FiberCoordinates) : Fin N → ℂ := fun j ↦ (s j).value i x v

def GivesClosedProjectiveEmbedding {V : AlgebraicRankTwoBundle} {n N : ℕ}
    (s : Fin N → SymmetricSection V n) : Prop :=
  (∀ i x, x ∈ V.domain i → ∀ v : FiberCoordinates, v ≠ 0 → sectionVector s i x v ≠ 0) ∧
  (∀ i j x y, x ∈ V.domain i → y ∈ V.domain j → ∀ v w : FiberCoordinates,
    v ≠ 0 → w ≠ 0 → (∃ c : ℂ, c ≠ 0 ∧ sectionVector s i x v = c • sectionVector s j y w) →
    x=y ∧ ∃ c : ℂ, c ≠ 0 ∧ v=c • ((V.dualTransition i j x).mulVec w)) ∧
  ProjectiveAlgebraicCone ({0} ∪ {a | ∃ i x, x ∈ V.domain i ∧
    ∃ v : FiberCoordinates, v ≠ 0 ∧ ∃ c : ℂ, c ≠ 0 ∧ a=c • sectionVector s i x v}) ∧
  ∀ i x, x ∈ V.domain i → ∀ v : FiberCoordinates, v ≠ 0 →
    ∃ j : Fin N, ∃ b : Fin 2, v b ≠ 0 ∧ sectionVector s i x v j ≠ 0 ∧
    ∃ p q : Fin 3 → MvPolynomial (Fin N) ℂ,
      (∀ k, MvPolynomial.eval (fun l ↦ sectionVector s i x v l / sectionVector s i x v j) (q k) ≠ 0) ∧
      ∀ i' x', x' ∈ V.domain i' → ∀ v' : FiberCoordinates, v' ≠ 0 →
        sectionVector s i' x' v' j ≠ 0 →
        (∀ k, MvPolynomial.eval (fun l ↦ sectionVector s i' x' v' l / sectionVector s i' x' v' j) (q k) ≠ 0) →
        x' ∈ V.domain i ∧ ((V.dualTransition i i' x').mulVec v') b ≠ 0 ∧
        (∀ k : Fin 3,
          (![ (coordQuadric (V.chart i) x').1, (coordQuadric (V.chart i) x').2,
             ((V.dualTransition i i' x').mulVec v') (1-b) /
               ((V.dualTransition i i' x').mulVec v') b ] : Fin 3 → ℂ) k =
          MvPolynomial.eval (fun l ↦ sectionVector s i' x' v' l / sectionVector s i' x' v' j) (p k) /
          MvPolynomial.eval (fun l ↦ sectionVector s i' x' v' l / sectionVector s i' x' v' j) (q k))

def IsAmple (V : AlgebraicRankTwoBundle) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ N : ℕ, ∃ s : Fin N → SymmetricSection V n,
    GivesClosedProjectiveEmbedding s

def holomorphicMetricDerivative (H : BaseCoordinates → TwoMatrix)
    (z u : BaseCoordinates) : TwoMatrix :=
  (1/2 : ℂ) • (fderiv ℝ H z u - Complex.I • fderiv ℝ H z (Complex.I • u))

def metricMixedHessian (H : BaseCoordinates → TwoMatrix)
    (z u : BaseCoordinates) : TwoMatrix :=
  (1/4 : ℂ) • ((fderiv ℝ (fun y ↦ fderiv ℝ H y) z u) u +
    (fderiv ℝ (fun y ↦ fderiv ℝ H y) z (Complex.I • u)) (Complex.I • u))

structure SmoothHermitianMetric (V : AlgebraicRankTwoBundle) where
  dualMatrix : ℕ → BaseCoordinates → TwoMatrix
  smooth : ∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dualMatrix i) (V.coordinateDomain i)
  positive : ∀ i z, z ∈ V.coordinateDomain i → (dualMatrix i z).PosDef
  compatible : ∀ i j x, x ∈ V.domain i → x ∈ V.domain j →
    dualMatrix j (coordQuadric (V.chart j) x) =
      (V.dualTransition i j x).conjTranspose * dualMatrix i (coordQuadric (V.chart i) x) *
        V.dualTransition i j x

def SmoothHermitianMetric.StrictlyGriffithsPositive {V : AlgebraicRankTwoBundle}
    (h : SmoothHermitianMetric V) : Prop :=
  ∀ i z, z ∈ V.coordinateDomain i → ∀ u : BaseCoordinates, u ≠ 0 →
    (metricMixedHessian (h.dualMatrix i) z u -
      (holomorphicMetricDerivative (h.dualMatrix i) z u).conjTranspose *
        (h.dualMatrix i z)⁻¹ * holomorphicMetricDerivative (h.dualMatrix i) z u).PosDef

def SourceMainTheorem : Prop :=
  ∃ G : AlgebraicRankTwoBundle, ∃ E : ℕ → AlgebraicRankTwoBundle,
    (∀ m, 0 < m → IsPowerPullbackTwist G m (E m)) ∧
    (∀ m, 0 < m → IsAmple (E m)) ∧
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m, m₀ ≤ m →
      ¬ ∃ h : SmoothHermitianMetric (E m), h.StrictlyGriffithsPositive

theorem main_theorem : SourceMainTheorem := by
  sorry

end QuadricCounterexample

end

end OAI
