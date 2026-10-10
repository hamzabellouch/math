import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

attribute [local instance] Classical.propDecidable

universe u

abbrev Euc (k : ℕ) := EuclideanSpace ℝ (Fin k)
abbrev Functional (X : Type u) (k : ℕ) := (X → ℝ) → (Fin k → X → ℝ) → ℝ

section MetricCurrents

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def BoundedLip (b : X → ℝ) : Prop :=
  (∃ K : ℝ≥0, LipschitzWith K b) ∧ ∃ M : ℝ, ∀ x, |b x| ≤ M

def Admissible {k : ℕ} (b : X → ℝ) (π : Fin k → X → ℝ) : Prop :=
  BoundedLip b ∧ ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)

def Controls {k : ℕ} (T : Functional X k) (μ : Measure X) : Prop :=
  ∀ (b : X → ℝ) (π : Fin k → X → ℝ), BoundedLip b →
    (∀ i, LipschitzWith 1 (π i)) →
    |T b π| ≤ ∫ x, |b x| ∂μ

noncomputable def mass {k : ℕ} (T : Functional X k) : ℝ :=
  sInf {r : ℝ | ∃ μ : Measure X,
    IsFiniteMeasure μ ∧ Controls T μ ∧ r = μ.real univ}

structure IsMetricCurrent {k : ℕ} (T : Functional X k) : Prop where
  offDomain : ∀ b π, ¬Admissible b π → T b π = 0
  linearFirst : ∀ b₁ b₂ π (a c : ℝ), BoundedLip b₁ → BoundedLip b₂ →
    (∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) →
    T (fun x => a * b₁ x + c * b₂ x) π = a * T b₁ π + c * T b₂ π
  linearCoord : ∀ b π i f (a c : ℝ), Admissible b π →
    (∃ K : ℝ≥0, LipschitzWith K f) →
    T b (Function.update π i (fun x => a * π i x + c * f x)) =
      a * T b π + c * T b (Function.update π i f)
  sequentialContinuity : ∀ b π (πs : ℕ → Fin k → X → ℝ), BoundedLip b →
    (∀ i, ∃ K : ℝ≥0, ∀ j, LipschitzWith K (πs j i)) →
    (∀ i x, Tendsto (fun j => πs j i x) atTop (𝓝 (π i x))) →
    Tendsto (fun j => T b (πs j)) atTop (𝓝 (T b π))
  locality : ∀ b π, Admissible b π →
    (∃ (i : Fin k) (U : Set X) (c : ℝ), IsOpen U ∧ Function.support b ⊆ U ∧
      ∀ x ∈ U, π i x = c) → T b π = 0
  finiteMass : ∃ μ : Measure X, IsFiniteMeasure μ ∧ Controls T μ

noncomputable def boundarySucc {k : ℕ} (T : Functional X (k + 1)) : Functional X k :=
  fun b π => if Admissible b π then T (fun _ => 1) (Matrix.vecCons b π) else 0

noncomputable def boundary : {k : ℕ} → Functional X k → Functional X (k - 1)
  | 0, _ => fun _ _ => 0
  | _ + 1, T => boundarySucc T

structure IntegerChart (X : Type u) [MetricSpace X] (k : ℕ) where
  domain : Set (Euc k)
  borel : MeasurableSet domain
  bounded : Bornology.IsBounded domain
  param : domain → X
  bilipschitz : ∃ L U : ℝ≥0, LipschitzWith L param ∧ AntilipschitzWith U param
  multiplicity : Euc k → ℤ
  integrable : Integrable (fun z => (multiplicity z : ℝ)) (volume.restrict domain)

namespace IntegerChart

variable {k : ℕ} (C : IntegerChart X k)

noncomputable def scalar (f : X → ℝ) (z : Euc k) : ℝ :=
  if hz : z ∈ C.domain then f (C.param ⟨z, hz⟩) else 0

noncomputable def jacobian (π : Fin k → X → ℝ) (z : Euc k) : ℝ :=
  Matrix.det (fun i j =>
    (fderivWithin ℝ (C.scalar (π i)) C.domain z) (EuclideanSpace.single j 1))

noncomputable def action : Functional X k :=
  fun b π => if Admissible b π then
    ∫ z in C.domain, (C.multiplicity z : ℝ) * C.scalar b z * C.jacobian π z
  else 0

def image : Set X := Set.range C.param

end IntegerChart

def IntegerRectifiable {k : ℕ} (T : Functional X k) : Prop :=
  ∃ C : ℕ → IntegerChart X k,
    Pairwise (fun i j => Disjoint (C i).image (C j).image) ∧
    (∀ i, IsMetricCurrent (C i).action) ∧
    Summable (fun i => mass (C i).action) ∧
    ∀ b π, T b π = ∑' i, (C i).action b π

def IsIntegral : (k : ℕ) → Functional X k → Prop
  | 0, T => IsMetricCurrent T ∧ IntegerRectifiable T
  | _ + 1, T => IsMetricCurrent T ∧ IntegerRectifiable T ∧
      IsMetricCurrent (boundarySucc T) ∧ IntegerRectifiable (boundarySucc T)

abbrev IntegralCurrent (X : Type u) [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (k : ℕ) := { T : Functional X k // IsIntegral k T }

def CompactlySupported {k : ℕ} (T : Functional X k) : Prop :=
  ∃ K : Set X, IsCompact K ∧
    ∀ b π, Admissible b π → (∀ x ∈ K, b x = 0) → T b π = 0

def IsCycle {k : ℕ} (T : Functional X k) : Prop := boundary T = fun _ _ => 0

end MetricCurrents

section Geometry
variable (X : Type u) [MetricSpace X]

def IsCAT0 : Prop :=
  ∃ segment : X → X → ℝ → X,
    (∀ x y, segment x y 0 = x ∧ segment x y 1 = y) ∧
    (∀ x y s t, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      dist (segment x y s) (segment x y t) = |s - t| * dist x y) ∧
    (∀ o x y s t, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      dist (segment o x s) (segment o y t) ^ 2 ≤
        (s * dist o x - t * dist o y) ^ 2 +
          s * t * ((dist x y) ^ 2 - (dist o x - dist o y) ^ 2))

end Geometry

noncomputable def omega (k : ℕ) : ℝ :=
  (volume (Metric.ball (0 : Euc k) 1)).toReal
noncomputable def sphereArea (n : ℕ) : ℝ := (n + 1 : ℝ) * omega (n + 1)
noncomputable def fillingCoefficient (n : ℕ) : ℝ :=
  1 / ((n + 1 : ℝ) * (sphereArea n) ^ (1 / (n : ℝ)))
noncomputable def fillingPower (n : ℕ) : ℝ := (n + 1 : ℝ) / (n : ℝ)

theorem sharp_integral_filling
    (X : Type u) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
    (hX : IsCAT0 X) (n : ℕ) (hn : 2 ≤ n) (T : IntegralCurrent X n)
    (hTc : CompactlySupported T.val) (hTz : IsCycle T.val) :
    ∃ S : IntegralCurrent X (n + 1), CompactlySupported S.val ∧
      boundarySucc S.val = T.val ∧
      mass S.val ≤ fillingCoefficient n * (mass T.val) ^ fillingPower n := by
  sorry

end CAT0Fillings

end OAI
