import Mathlib

namespace OAI


open MeasureTheory Set Filter
open scoped ENNReal Topology Manifold ContDiff

namespace SmoothObstruction

/-- Shannon entropy in bits; the value at mass zero is zero. -/
noncomputable def entropyTerm (p : ℝ) : ℝ := -(p * Real.log p) / Real.log 2

/-- The entropy of the length-`n` join of the partition with labels in `Fin q`. -/
noncomputable def blockEntropy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : X → X) {q : ℕ} (P : X → Fin q) (n : ℕ) : ℝ :=
  ∑ w : Fin n → Fin q,
    entropyTerm ((μ {x | ∀ j : Fin n, P ((T^[j.val]) x) = w j}).toReal)

/-- All finite-partition entropy rates exist and have one finite real upper
bound. This spells out `sup_P lim_n H(join_{j<n} T^{-j}P)/n < ∞` without
choosing a value for limits of nonconvergent sequences. Empty atoms are allowed. -/
def FiniteKSEntropy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : X → X) : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) (P : X → Fin (q + 1)), Measurable P →
    ∃ h : ℝ, h ≤ C ∧
      Tendsto (fun n : ℕ => blockEntropy μ T P n / (n : ℝ)) atTop (𝓝 h)

/-- Measure-space isomorphism after removing measurable null sets. -/
def ConullIsomorphic {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) : Prop :=
  ∃ (A : Set X) (B : Set Y), MeasurableSet A ∧ MeasurableSet B ∧
    μ Aᶜ = 0 ∧ ν Bᶜ = 0 ∧
    ∃ e : A ≃ᵐ B,
      MeasurePreserving e (μ.comap (Subtype.val : A → X))
        (ν.comap (Subtype.val : B → Y))

/-- Standard nonatomic in the source's explicit modulo-null-set sense. -/
def StandardNonatomic {X : Type*} [MeasurableSpace X] (μ : Measure X) : Prop :=
  ConullIsomorphic μ
    (volume.comap (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ))

/-- Measurable conjugacy on invariant conull measurable subsets, not a
continuous conjugacy and not merely a factor map. -/
def ConullConjugate {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (T : X → X) (ν : Measure Y) (S : Y → Y) : Prop :=
  ∃ (A : Set X) (B : Set Y), MeasurableSet A ∧ MeasurableSet B ∧
    μ Aᶜ = 0 ∧ ν Bᶜ = 0 ∧ T ⁻¹' A = A ∧ S ⁻¹' B = B ∧
    ∃ e : A ≃ᵐ B,
      MeasurePreserving e (μ.comap (Subtype.val : A → X))
        (ν.comap (Subtype.val : B → Y)) ∧
      ∀ (x y : A), T x = y → (e y : Y) = S (e x)

/-- Positive smooth local coordinate densities. In a half-space chart,
`ContDiffOn` includes smoothness up to the boundary. Absolute Lebesgue density
is used; no orientation or volume form is part of the data. -/
def SmoothPositiveDensity {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M]
    (ν : Measure M) : Prop :=
  ∀ x : M, ∃ f : EuclideanSpace ℝ (Fin d) → ℝ,
    ContDiffOn ℝ ∞ f (extChartAt I x).target ∧
    (∀ y ∈ (extChartAt I x).target, 0 < f y) ∧
    Measure.map (extChartAt I x) (ν.restrict (extChartAt I x).source) =
      (volume.withDensity (fun y => ENNReal.ofReal (f y))).restrict
        (extChartAt I x).target

/-- A smooth positive-volume model with a specified Euclidean or half-space
manifold model. All model dimensions will be quantified below. -/
def HasModelWith {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : X → X) {d : ℕ} {H : Type} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H) : Prop :=
  ∃ (M : Type) (_ : TopologicalSpace M) (_ : MeasurableSpace M)
      (_ : BorelSpace M) (_ : T2Space M) (_ : SecondCountableTopology M)
      (_ : CompactSpace M) (_ : ChartedSpace H M) (_ : IsManifold I ∞ M)
      (ν : Measure M) (_ : IsProbabilityMeasure ν)
      (S : Diffeomorph I I M M ∞),
    SmoothPositiveDensity I ν ∧ MeasurePreserving S ν ν ∧
      ConullConjugate μ T ν S

/-- Closed manifolds of all dimensions (including zero), and smooth manifolds
with boundary of every positive finite dimension. Nonorientable manifolds
are included: no orientability hypothesis occurs. -/
def HasSmoothPositiveVolumeModel {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : X → X) : Prop :=
  (∃ d : ℕ, HasModelWith μ T (𝓡 d)) ∨
    (∃ d : ℕ, ∃ _ : NeZero d, HasModelWith μ T (𝓡∂ d))

/-- A finite-entropy standard nonatomic ergodic system with no smooth positive-volume model. -/
theorem main :
    ∃ (X : Type) (_ : MeasurableSpace X) (μ : Measure X)
      (_ : IsProbabilityMeasure μ) (T : X ≃ᵐ X),
      StandardNonatomic μ ∧ Ergodic T μ ∧ FiniteKSEntropy μ T ∧
        ¬ HasSmoothPositiveVolumeModel μ T := by
  sorry

end SmoothObstruction

end OAI
