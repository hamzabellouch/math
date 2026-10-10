import OAI.Analysis.CircleDomains.Sobolev.MetricTensor
import OAI.Analysis.CircleDomains.Sobolev.FiniteEnergy
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Matrix.Normed

namespace OAI

/-!
# Choosing the actual metric from the coordinate differentials

The Gram tensor is the sum of the rank-one coordinate tensors.
Regularization makes it a positive definite metric, and the integral
bound is for its actual inverse-matrix energy density.
-/

open Matrix MeasureTheory Finset
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def gramTensor (x y : ℕ → ℝ) (n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  symmetricTensor (∑ i ∈ range n, x i ^ 2) (∑ i ∈ range n, x i * y i)
    (∑ i ∈ range n, y i ^ 2)

theorem gramTensor_eq_sum (x y : ℕ → ℝ) (n : ℕ) :
    gramTensor x y n = ∑ i ∈ range n, Matrix.vecMulVec ![x i, y i] ![x i, y i] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gramTensor, symmetricTensor, Matrix.vecMulVec, Matrix.sum_apply, pow_two, mul_comm]

theorem gramTensor_posSemidef (x y : ℕ → ℝ) (n : ℕ) : (gramTensor x y n).PosSemidef := by
  rw [gramTensor_eq_sum]
  apply Matrix.posSemidef_sum
  intro i _
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star ![x i, y i]

theorem gramTensor_energy {τ : ℝ} (hτ : 0 < τ) (x y : ℕ → ℝ) (n : ℕ) :
    Matrix.trace ((gramTensor x y n + τ • 1)⁻¹ * gramTensor x y n) *
      Real.sqrt (gramTensor x y n + τ • 1).det =
      tensorEnergy (covectorTrace x y n) (covectorDet x y n) τ := by
  exact trace_inverse_energy_eq_tensorEnergy
    (sum_nonneg (fun _ _ => sq_nonneg _)) (sum_nonneg (fun _ _ => sq_nonneg _))
    (covectorDet_nonneg x y n) hτ

/-- Small pairwise wedge integrals give one positive definite metric with
small total coordinate energy. All tensor and inverse formulas are derived. -/
theorem exists_gramMetric_energy_lt
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (x y : ℕ → X → ℝ) (n : ℕ)
    (hx : ∀ i, Measurable (x i)) (hy : ∀ i, Measurable (y i))
    (htrace : Integrable (fun z => covectorTrace (fun i => x i z) (fun i => y i z) n) μ)
    (hwedge : Integrable (fun z => covectorWedges (fun i => x i z) (fun i => y i z) n) μ)
    {ε : ℝ} (hε : (∫ z, 2 * covectorWedges (fun i => x i z) (fun i => y i z) n ∂μ) < ε) :
    ∃ τ : ℝ, 0 < τ ∧
      (∀ z, (gramTensor (fun i => x i z) (fun i => y i z) n + τ • 1).PosDef) ∧
      (∫ z, Matrix.trace
        ((gramTensor (fun i => x i z) (fun i => y i z) n + τ • 1)⁻¹ *
          gramTensor (fun i => x i z) (fun i => y i z) n) *
        Real.sqrt (gramTensor (fun i => x i z) (fun i => y i z) n + τ • 1).det ∂μ) < ε := by
  obtain ⟨τ, hτ, henergy⟩ := exists_regularization_energy_lt x y n hx hy htrace hwedge hε
  refine ⟨τ, hτ, fun z => ?_, ?_⟩
  · exact Matrix.PosDef.posSemidef_add (gramTensor_posSemidef _ _ _)
      (Matrix.PosDef.one.smul hτ)
  · simpa only [gramTensor_energy hτ] using henergy

/-- For smooth coordinate differentials on a bounded planar region,
integrability is automatic and the chosen positive definite metric is
itself smooth. -/
theorem exists_smooth_gramMetric_on_bounded
    (x y : ℕ → (ℝ × ℝ) → ℝ) (n : ℕ)
    (hx : ∀ i, ContDiff ℝ ∞ (x i)) (hy : ∀ i, ContDiff ℝ ∞ (y i))
    {S : Set (ℝ × ℝ)} (hS : Bornology.IsBounded S) {ε : ℝ}
    (hε : (∫ z in S, 2 * covectorWedges (fun i => x i z) (fun i => y i z) n) < ε) :
    ∃ τ : ℝ, 0 < τ ∧
      ContDiff ℝ ∞ (fun z => gramTensor (fun i => x i z) (fun i => y i z) n + τ • 1) ∧
      (∀ z, (gramTensor (fun i => x i z) (fun i => y i z) n + τ • 1).PosDef) ∧
      (∫ z in S, Matrix.trace
        ((gramTensor (fun i => x i z) (fun i => y i z) n + τ • 1)⁻¹ *
          gramTensor (fun i => x i z) (fun i => y i z) n) *
        Real.sqrt (gramTensor (fun i => x i z) (fun i => y i z) n + τ • 1).det) < ε := by
  have hT : Continuous (fun z => covectorTrace (fun i => x i z) (fun i => y i z) n) := by
    unfold covectorTrace
    fun_prop
  have hW : Continuous (fun z => covectorWedges (fun i => x i z) (fun i => y i z) n) := by
    unfold covectorWedges
    fun_prop
  have hTi : IntegrableOn (fun z => covectorTrace (fun i => x i z) (fun i => y i z) n) S :=
    (hT.continuousOn.integrableOn_compact hS.isCompact_closure).mono_set subset_closure
  have hWi : IntegrableOn (fun z => covectorWedges (fun i => x i z) (fun i => y i z) n) S :=
    (hW.continuousOn.integrableOn_compact hS.isCompact_closure).mono_set subset_closure
  obtain ⟨τ, hτ, hPD, hE⟩ := exists_gramMetric_energy_lt x y n
    (fun i => (hx i).continuous.measurable) (fun i => (hy i).continuous.measurable) hTi hWi hε
  refine ⟨τ, hτ, ?_, hPD, hE⟩
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [gramTensor, symmetricTensor]
    <;> fun_prop

end CircleDomainRigidity.FiniteTransfer

end

end OAI
