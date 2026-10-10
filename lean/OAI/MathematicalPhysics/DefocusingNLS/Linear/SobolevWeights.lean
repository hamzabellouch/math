import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

namespace OAI

/-!
# Summability of the twelve-dimensional Gaussian Sobolev variances

The exponent restriction in Corollary 1.2 is exactly `α > k + 6`.
We use the Euclidean integer lattice, defined as the integer span of the
standard orthonormal basis, and the existing lattice p-series theorem.
-/

namespace DefocusingNLS

/-- The standard Fourier frequency lattice in twelve dimensions. -/
noncomputable def frequencyLattice : Submodule ℤ (EuclideanSpace ℝ (Fin 12)) :=
  Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin 12) ℝ).toBasis)

instance : DiscreteTopology frequencyLattice := by
  unfold frequencyLattice
  infer_instance

instance : IsZLattice ℝ frequencyLattice := by
  unfold frequencyLattice
  infer_instance

/-- The frequency lattice has integer rank twelve. -/
theorem frequencyLattice_rank : Module.finrank ℤ frequencyLattice = 12 := by
  rw [ZLattice.rank ℝ frequencyLattice]
  exact finrank_euclideanSpace_fin

/-- The square Sobolev weights of the Gaussian coefficients are summable.
The lattice norm here is the Euclidean norm, as in the manuscript. -/
theorem summable_sobolev_variances (k α : ℝ) (hα : k + 6 < α) :
    Summable (fun n : frequencyLattice => (1 + ‖n‖ ^ 2) ^ (k - α)) := by
  classical
  have hexp : k - α < 0 := by linarith
  have hlattice : Summable (fun n : frequencyLattice => ‖n‖ ^ (2 * (k - α))) := by
    apply ZLattice.summable_norm_rpow frequencyLattice
    rw [frequencyLattice_rank]
    norm_num
    linarith
  have hsingle : Summable (fun n : frequencyLattice => if n = 0 then (1 : ℝ) else 0) :=
    (hasSum_ite_eq 0 1).summable
  apply Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (by positivity) _) _
    (hsingle.add hlattice)
  intro n
  by_cases hn : n = 0
  · simp [hn, Real.zero_rpow (by linarith : 2 * (k - α) ≠ 0)]
  · have hnorm : 0 < ‖n‖ := norm_pos_iff.mpr hn
    simp only [hn, ↓reduceIte, zero_add]
    calc
      (1 + ‖n‖ ^ 2) ^ (k - α) ≤ (‖n‖ ^ 2) ^ (k - α) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hexp.le
      _ = ‖n‖ ^ (2 * (k - α)) := by
        rw [Real.rpow_mul (norm_nonneg n)]
        norm_num

end DefocusingNLS

end OAI
