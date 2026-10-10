import Mathlib.Probability.CondVar
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Process.Filtration

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.IndependentTrials

universe u v

variable {T : ℕ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {A : Fin T → Type v} [∀ i, MeasurableSpace (A i)]

def trialVector (ξ : (i : Fin T) → Ω → A i) (ω : Ω) : (i : Fin T) → A i :=
  fun i ↦ ξ i ω

def prefixIndices (T n : ℕ) : Finset (Fin T) :=
  Finset.univ.filter (fun i ↦ i.val < n)

def prefixFiltration (ξ : (i : Fin T) → Ω → A i)
    (hξ : ∀ i, Measurable (ξ i)) : Filtration ℕ mΩ where
  seq n := (Filtration.piFinset (X := A) (prefixIndices T n)).comap (trialVector ξ)
  mono' n k hnk := by
    apply MeasurableSpace.comap_mono
    apply Filtration.mono
    intro i hi
    simp only [prefixIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact lt_of_lt_of_le hi hnk
  le' n := by
    exact (MeasurableSpace.comap_mono (Filtration.piFinset.le (prefixIndices T n))).trans
      (Measurable.of_eval hξ).comap_le

def doobProcess (ξ : (i : Fin T) → Ω → A i)
    (hξ : ∀ i, Measurable (ξ i)) (Y : Ω → ℝ) (μ : Measure Ω) (n : ℕ) : Ω → ℝ :=
  μ[Y | prefixFiltration ξ hξ n]

def CoordinateOscillation (F : ((i : Fin T) → A i) → ℝ) (c : Fin T → ℝ) : Prop :=
  ∀ i x y, (∀ j, j ≠ i → x j = y j) → |F x - F y| ≤ c i

end IndependentTrials

open IndependentTrials

universe u v

def IndependentTrialJumps : Prop :=
  ∀ (T : ℕ) (Ω : Type u) (_mΩ : MeasurableSpace Ω) (μ : Measure Ω),
  ∀ [IsProbabilityMeasure μ],
  ∀ (A : Fin T → Type v) (_mA : ∀ i, MeasurableSpace (A i)),
  ∀ (ξ : (i : Fin T) → Ω → A i) (hξ : ∀ i, Measurable (ξ i)),
  ∀ (F : ((i : Fin T) → A i) → ℝ), Measurable F →
    ProbabilityTheory.iIndepFun ξ μ →
    Integrable (fun ω ↦ F (trialVector ξ ω)) μ →
  ∀ (c : Fin T → ℝ), (∀ i, 0 ≤ c i) → CoordinateOscillation F c →
    let Y : Ω → ℝ := fun ω ↦ F (trialVector ξ ω)
    let D := doobProcess ξ hξ Y μ
    (D 0 =ᵐ[μ] fun _ ↦ ∫ ω, Y ω ∂μ) ∧
    (D T =ᵐ[μ] Y) ∧
    (∀ i : Fin T,
      (∀ᵐ ω ∂μ, |D (i.val + 1) ω - D i.val ω| ≤ c i) ∧
      (∀ᵐ ω ∂μ, ProbabilityTheory.condVar (prefixFiltration ξ hξ i.val)
        (fun x ↦ D (i.val + 1) x - D i.val x) μ ω ≤ (c i) ^ 2)) ∧
    (∀ (L u : ℝ), 1 ≤ T → 0 < L → (∀ i, c i ≤ L) → 0 < u →
      μ.real {ω | u ≤ |Y ω - ∫ x, Y x ∂μ|} ≤
        2 * Real.exp (-(u ^ 2) / (8 * (T : ℝ) * L ^ 2)))

end Balanced

end

end OAI
