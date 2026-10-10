import OAI.Analysis.CircleDomains.Sobolev.WedgeEnergy

namespace OAI

/-!
# From a positive two-dimensional tensor to optimized energy

The trace and determinant determine the energy of `A + τ I`. The scalar
roots used below are the two nonnegative eigenvalues, constructed directly
from the characteristic polynomial. This connects the metric limit to
the Gram determinant of the actual finite list of coordinate differentials.
-/

open Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def upperRoot (T D : ℝ) : ℝ := (T + Real.sqrt (T ^ 2 - 4 * D)) / 2
def lowerRoot (T D : ℝ) : ℝ := (T - Real.sqrt (T ^ 2 - 4 * D)) / 2

theorem roots_nonneg {T D : ℝ} (hT : 0 ≤ T) (hD : 0 ≤ D) :
    0 ≤ upperRoot T D ∧ 0 ≤ lowerRoot T D := by
  have hs : Real.sqrt (T ^ 2 - 4 * D) ≤ T :=
    Real.sqrt_le_iff.mpr ⟨hT, by nlinarith⟩
  constructor
  · unfold upperRoot
    positivity
  · unfold lowerRoot
    linarith

theorem roots_sum (T D : ℝ) : upperRoot T D + lowerRoot T D = T := by
  unfold upperRoot lowerRoot
  ring

theorem roots_product {T D : ℝ} (hdisc : 0 ≤ T ^ 2 - 4 * D) :
    upperRoot T D * lowerRoot T D = D := by
  have hs := Real.sq_sqrt hdisc
  unfold upperRoot lowerRoot
  nlinarith

/-- The coordinate-invariant expression for the regularized energy density. -/
def tensorEnergy (T D τ : ℝ) : ℝ :=
  (2 * D + τ * T) / Real.sqrt (D + τ * T + τ ^ 2)

theorem tensorEnergy_eq_metricEnergy {T D τ : ℝ}
    (hT : 0 ≤ T) (hD : 0 ≤ D) (hdisc : 0 ≤ T ^ 2 - 4 * D) (hτ : 0 < τ) :
    tensorEnergy T D τ = metricEnergy (upperRoot T D) (lowerRoot T D) τ := by
  obtain ⟨hhi, hlo⟩ := roots_nonneg hT hD
  have hp := roots_product hdisc
  have hs := roots_sum T D
  rw [metricEnergy_eq_density hhi hlo hτ]
  have hn : 2 * upperRoot T D * lowerRoot T D +
      τ * (upperRoot T D + lowerRoot T D) = 2 * D + τ * T := by
    rw [hs]
    nlinarith [hp]
  have hd : (upperRoot T D + τ) * (lowerRoot T D + τ) = D + τ * T + τ ^ 2 := by
    nlinarith [hp, hs]
  rw [hn, hd]
  rfl

theorem tensorEnergy_le_trace {T D τ : ℝ}
    (hT : 0 ≤ T) (hD : 0 ≤ D) (hdisc : 0 ≤ T ^ 2 - 4 * D) (hτ : 0 < τ) :
    tensorEnergy T D τ ≤ T := by
  rw [tensorEnergy_eq_metricEnergy hT hD hdisc hτ]
  exact (metricEnergy_le_trace (roots_nonneg hT hD).1 (roots_nonneg hT hD).2 hτ).trans_eq
    (roots_sum T D)

theorem tendsto_tensorEnergy {T D : ℝ}
    (hT : 0 ≤ T) (hD : 0 ≤ D) (hdisc : 0 ≤ T ^ 2 - 4 * D) :
    Tendsto (tensorEnergy T D) (𝓝[>] 0) (𝓝 (2 * Real.sqrt D)) := by
  have h := tendsto_metricEnergy (roots_nonneg hT hD).1 (roots_nonneg hT hD).2
  rw [roots_product hdisc] at h
  apply h.congr'
  filter_upwards [show ∀ᶠ τ : ℝ in 𝓝[>] 0, 0 < τ from self_mem_nhdsWithin] with τ hτ
  exact (tensorEnergy_eq_metricEnergy hT hD hdisc hτ).symm

/-- Dominated convergence in terms of the tensor invariants. -/
theorem tendsto_integral_tensorEnergy {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {T D : X → ℝ} (hT : Measurable T) (hD : Measurable D)
    (hT0 : ∀ x, 0 ≤ T x) (hD0 : ∀ x, 0 ≤ D x)
    (hdisc : ∀ x, 0 ≤ T x ^ 2 - 4 * D x) (htrace : Integrable T μ) :
    Tendsto (fun τ : ℝ => ∫ x, tensorEnergy (T x) (D x) τ ∂μ) (𝓝[>] 0)
      (𝓝 (∫ x, 2 * Real.sqrt (D x) ∂μ)) := by
  have hmeas (τ : ℝ) : Measurable (fun x => tensorEnergy (T x) (D x) τ) := by
    unfold tensorEnergy
    fun_prop
  apply tendsto_integral_filter_of_dominated_convergence T
  · exact Filter.Eventually.of_forall fun τ => (hmeas τ).aestronglyMeasurable
  · filter_upwards [show ∀ᶠ τ : ℝ in 𝓝[>] 0, 0 < τ from self_mem_nhdsWithin] with τ hτ
    apply Filter.Eventually.of_forall
    intro x
    have hn : 0 ≤ tensorEnergy (T x) (D x) τ := by
      have ht := hT0 x
      have hd := hD0 x
      unfold tensorEnergy
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact tensorEnergy_le_trace (hT0 x) (hD0 x) (hdisc x) hτ
  · exact htrace
  · exact Filter.Eventually.of_forall fun x => tendsto_tensorEnergy (hT0 x) (hD0 x) (hdisc x)

/-- Trace of the Gram tensor formed from a finite list of planar covectors. -/
def covectorTrace (x y : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, x i ^ 2) + (∑ i ∈ Finset.range n, y i ^ 2)

/-- Determinant of the same Gram tensor. -/
def covectorDet (x y : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, x i ^ 2) * (∑ i ∈ Finset.range n, y i ^ 2) -
    (∑ i ∈ Finset.range n, x i * y i) ^ 2

theorem covectorTrace_nonneg (x y : ℕ → ℝ) (n : ℕ) : 0 ≤ covectorTrace x y n := by
  unfold covectorTrace
  positivity

theorem covectorDet_nonneg (x y : ℕ → ℝ) (n : ℕ) : 0 ≤ covectorDet x y n := by
  unfold covectorDet
  rw [gramDet_eq_wedgeSquares]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem covector_discriminant_nonneg (x y : ℕ → ℝ) (n : ℕ) :
    0 ≤ covectorTrace x y n ^ 2 - 4 * covectorDet x y n := by
  unfold covectorTrace covectorDet
  nlinarith [sq_nonneg ((∑ i ∈ Finset.range n, x i ^ 2) -
    (∑ i ∈ Finset.range n, y i ^ 2)), sq_nonneg (∑ i ∈ Finset.range n, x i * y i)]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
