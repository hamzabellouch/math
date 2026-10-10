import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

namespace OAI

/-! # Passing finite affine fits through convergence of actual L² moments

Only the finitely many pairings of the target, constant and coordinate
functions are needed. The spaces containing them may vary with the index.
This is the algebraic step following local strong L² compactness.
-/

open Filter
open scoped InnerProductSpace Topology BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {ι : Type*} [Fintype ι]

/-- The squared norm of a finite linear combination uses precisely its
finite Gram matrix. -/
theorem norm_sum_smul_sq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : ι → H) (a : ι → ℝ) :
    ‖∑ i, a i • f i‖ ^ 2 = ∑ i, ∑ j, a i * a j * ⟪f i, f j⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_comm (f j) (f i)]
  ring

/-- Joint local L² convergence implies convergence of every fixed affine
fit error, without choosing minimizers or identifying the varying spaces. -/
theorem norm_sum_smul_tendsto_of_inner_tendsto
    {H : ℕ → Type*} [∀ k, NormedAddCommGroup (H k)]
    [∀ k, InnerProductSpace ℝ (H k)]
    {Hlim : Type*} [NormedAddCommGroup Hlim] [InnerProductSpace ℝ Hlim]
    (f : ∀ k, ι → H k) (flim : ι → Hlim)
    (h : ∀ i j, Tendsto (fun k => ⟪f k i, f k j⟫_ℝ) atTop (𝓝 ⟪flim i, flim j⟫_ℝ))
    (a : ι → ℝ) :
    Tendsto (fun k => ‖∑ i, a i • f k i‖) atTop (𝓝 ‖∑ i, a i • flim i‖) := by
  have hs : Tendsto (fun k => ‖∑ i, a i • f k i‖ ^ 2) atTop
      (𝓝 (‖∑ i, a i • flim i‖ ^ 2)) := by
    simp only [norm_sum_smul_sq]
    apply tendsto_finsetSum
    intro i hi
    apply tendsto_finsetSum
    intro j hj
    exact tendsto_const_nhds.mul (h i j)
  have hr := (Real.continuous_sqrt.tendsto _).comp hs
  change Tendsto (fun k => Real.sqrt (‖∑ i, a i • f k i‖ ^ 2)) atTop
    (𝓝 (Real.sqrt (‖∑ i, a i • flim i‖ ^ 2))) at hr
  simpa only [Real.sqrt_sq_eq_abs, abs_norm] using hr

/-- A strict bound on one Euclidean candidate is inherited by the actual
finite linear combinations for all sufficiently late indices. -/
theorem eventually_norm_sum_smul_lt
    {H : ℕ → Type*} [∀ k, NormedAddCommGroup (H k)]
    [∀ k, InnerProductSpace ℝ (H k)]
    {Hlim : Type*} [NormedAddCommGroup Hlim] [InnerProductSpace ℝ Hlim]
    (f : ∀ k, ι → H k) (flim : ι → Hlim)
    (h : ∀ i j, Tendsto (fun k => ⟪f k i, f k j⟫_ℝ) atTop (𝓝 ⟪flim i, flim j⟫_ℝ))
    (a : ι → ℝ) {η : ℝ} (hη : ‖∑ i, a i • flim i‖ < η) :
    ∀ᶠ k in atTop, ‖∑ i, a i • f k i‖ < η :=
  (norm_sum_smul_tendsto_of_inner_tendsto f flim h a).eventually (gt_mem_nhds hη)

end RegularPointCoordinates

end

end OAI
