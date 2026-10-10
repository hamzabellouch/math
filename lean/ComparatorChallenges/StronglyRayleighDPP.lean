import Mathlib

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Topology ComplexConjugate

namespace Problem336AdditiveD139

abbrev UnitLabel := Set.Icc (0 : ℝ) 1

def leftTranslate {Γ : Type u_1} {α : Type u_2} [Group Γ] (g : Γ) (a : Γ → α) : Γ → α :=
  fun h => a (g⁻¹ * h)

def iidUnitLabels (Γ : Type u_3) [MeasurableSpace Γ] : Measure (Γ → UnitLabel) :=
  Measure.infinitePi (fun _ : Γ => (volume : Measure UnitLabel))

def InvariantBinaryLaw {Γ : Type u_4} [Group Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) : Prop :=
  ∀ g : Γ,
    Measure.map (leftTranslate g) (μ : Measure (Γ → Bool)) =
      (μ : Measure (Γ → Bool))

def HasEquivariantIIDFactor {Γ : Type u_5} [Group Γ] [MeasurableSpace Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) : Prop :=
  ∃ Phi : (Γ → UnitLabel) → (Γ → Bool),
    Measurable Phi ∧
    (∀ (g : Γ) (u : Γ → UnitLabel),
      Phi (leftTranslate g u) = leftTranslate g (Phi u)) ∧
    Measure.map Phi (iidUnitLabels Γ) = (μ : Measure (Γ → Bool))

def finiteGeneratingValue {F : Type u_6} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (z : F → ℂ) : ℂ := by
  classical
  exact ∑ x : F → Bool,
    (((μ : Measure (F → Bool)) {x}).toReal : ℂ) *
      ∏ i : F, if x i = true then z i else 1

def StronglyRayleighFinite {F : Type u_7} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) : Prop :=
  ∀ z : F → ℂ, (∀ i : F, 0 < (z i).im) → finiteGeneratingValue μ z ≠ 0

def marginalMass {I : Type u_8} (μ : ProbabilityMeasure (I → Bool))
    (S : Finset I) (x : S → Bool) : ℝ :=
  ((μ : Measure (I → Bool)) {a | ∀ i : S, a i.1 = x i}).toReal

def marginalGeneratingValue {I : Type u_9} (μ : ProbabilityMeasure (I → Bool))
    (S : Finset I) (z : S → ℂ) : ℂ := by
  classical
  exact ∑ x : S → Bool,
    (marginalMass μ S x : ℂ) *
      ∏ i : S, if x i = true then z i else 1

def StronglyRayleighCountable {I : Type u_10}
    (μ : ProbabilityMeasure (I → Bool)) : Prop :=
  ∀ S : Finset I, ∀ z : S → ℂ,
    (∀ i : S, 0 < (z i).im) → marginalGeneratingValue μ S z ≠ 0

def boolReal (b : Bool) : ℝ := if b = true then 1 else 0

def tiltPartition {F : Type u_11} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) : ℝ := by
  classical
  exact ∑ x : F → Bool,
    Real.exp (∑ j : F, h j * boolReal (x j)) *
      ((μ : Measure (F → Bool)) {x}).toReal

def tiltMean {F : Type u_12} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i : F) : ℝ := by
  classical
  exact (∑ x : F → Bool,
      Real.exp (∑ j : F, h j * boolReal (x j)) *
        ((μ : Measure (F → Bool)) {x}).toReal * boolReal (x i)) /
    tiltPartition μ h

def tiltSecondMoment {F : Type u_13} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i j : F) : ℝ := by
  classical
  exact (∑ x : F → Bool,
      Real.exp (∑ k : F, h k * boolReal (x k)) *
        ((μ : Measure (F → Bool)) {x}).toReal *
        boolReal (x i) * boolReal (x j)) /
    tiltPartition μ h

def tiltCovariance {F : Type u_14} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i j : F) : ℝ :=
  tiltSecondMoment μ h i j - tiltMean μ h i * tiltMean μ h j

def coordinatePerturb {F : Type u_15} (h : F → ℝ) (j : F) (r : ℝ) : F → ℝ := by
  classical
  exact fun k => h k + if k = j then r else 0

def PositiveContractionFinite {F : Type u_16} [Fintype F]
    (K : F → F → ℂ) : Prop :=
  (∀ i j, K i j = conj (K j i)) ∧
  ∀ c : F → ℂ,
    0 ≤ (∑ i : F, ∑ j : F, conj (c i) * K i j * c j).re ∧
    (∑ i : F, ∑ j : F, conj (c i) * K i j * c j).re ≤
      ∑ i : F, Complex.normSq (c i)

def IsFiniteDeterminantalLaw {F : Type u_17} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (K : F → F → ℂ) : Prop := by
  classical
  exact ∀ A : Finset F,
    (((μ : Measure (F → Bool)) {x | ∀ i ∈ A, x i = true}).toReal : ℂ) =
      Matrix.det (fun i j : A => K i.1 j.1)

def PositiveContractionKernel {I : Type u_18}
    (K : I → I → ℂ) : Prop :=
  (∀ i j, K i j = conj (K j i)) ∧
  ∀ (S : Finset I) (c : S → ℂ),
    0 ≤ (∑ i : S, ∑ j : S, conj (c i) * K i.1 j.1 * c j).re ∧
    (∑ i : S, ∑ j : S, conj (c i) * K i.1 j.1 * c j).re ≤
      ∑ i : S, Complex.normSq (c i)

def IsDeterminantalLaw {I : Type u_19}
    (μ : ProbabilityMeasure (I → Bool)) (K : I → I → ℂ) : Prop := by
  classical
  exact ∀ A : Finset I,
    (((μ : Measure (I → Bool)) {x | ∀ i ∈ A, x i = true}).toReal : ℂ) =
      Matrix.det (fun i j : A => K i.1 j.1)

def TranslationInvariantKernel {Γ : Type u_20} [Group Γ]
    (K : Γ → Γ → ℂ) : Prop :=
  ∀ g h k : Γ, K (g * h) (g * k) = K h k

theorem finite_strongly_rayleigh_response :
    ∀ (F : Type u_1) [Fintype F] [Nonempty F] (μ : ProbabilityMeasure (F → Bool)),
      StronglyRayleighFinite μ →
        (∀ (i j : F) (h : F → ℝ),
          HasDerivAt (fun r : ℝ => tiltMean μ (coordinatePerturb h j r) i)
            (tiltCovariance μ h i j) 0) ∧
        (∀ (i : F) (h : F → ℝ),
          (∑ j : F, |tiltCovariance μ h i j|) ≤
              2 * tiltMean μ h i * (1 - tiltMean μ h i) ∧
            2 * tiltMean μ h i * (1 - tiltMean μ h i) ≤ (1 : ℝ) / 2) ∧
        (∀ (i : F) (h h' : F → ℝ) (D : ℝ),
          0 ≤ D → (∀ j : F, |h j - h' j| ≤ D) →
            |tiltMean μ h i - tiltMean μ h' i| ≤ D / 2) := by
  sorry

theorem strongly_rayleigh_group_factor :
    ∀ (Γ : Type u_2) [Group Γ] [Countable Γ] [MeasurableSpace Γ],
      ∀ μ : ProbabilityMeasure (Γ → Bool),
        StronglyRayleighCountable μ → InvariantBinaryLaw μ → HasEquivariantIIDFactor μ := by
  sorry

theorem finite_positive_contraction_dpp_is_strongly_rayleigh :
    ∀ (F : Type u_3) [Fintype F] [Nonempty F] (K : F → F → ℂ),
      PositiveContractionFinite K →
        (∃ μ : ProbabilityMeasure (F → Bool), IsFiniteDeterminantalLaw μ K) ∧
          ∀ μ : ProbabilityMeasure (F → Bool), IsFiniteDeterminantalLaw μ K →
            StronglyRayleighFinite μ := by
  sorry

theorem countable_positive_contraction_dpp_exists_unique :
    ∀ (I : Type u_4) [Countable I] (K : I → I → ℂ),
      PositiveContractionKernel K →
        ∃! μ : ProbabilityMeasure (I → Bool), IsDeterminantalLaw μ K := by
  sorry

theorem invariant_positive_contraction_dpp_factor :
    ∀ (Γ : Type u_5) [Group Γ] [Countable Γ] [MeasurableSpace Γ]
      (K : Γ → Γ → ℂ) (μ : ProbabilityMeasure (Γ → Bool)),
      PositiveContractionKernel K → IsDeterminantalLaw μ K →
        InvariantBinaryLaw μ → HasEquivariantIIDFactor μ := by
  sorry

theorem translation_invariant_kernel_dpp_factor :
    ∀ (Γ : Type u_6) [Group Γ] [Countable Γ] [MeasurableSpace Γ] (K : Γ → Γ → ℂ),
      PositiveContractionKernel K → TranslationInvariantKernel K →
        ∃ μ : ProbabilityMeasure (Γ → Bool),
          IsDeterminantalLaw μ K ∧ InvariantBinaryLaw μ ∧ HasEquivariantIIDFactor μ := by
  sorry

end Problem336AdditiveD139

end

end OAI
