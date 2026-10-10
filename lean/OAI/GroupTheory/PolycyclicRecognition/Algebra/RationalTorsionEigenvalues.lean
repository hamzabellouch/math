import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundedDegreeRootsOfUnity
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteOrderMatrixTraces
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

namespace OAI

/-! # Bounded algebraic degrees for eigenvalues of rational torsion matrices -/

noncomputable section
namespace PolycyclicRecognition
open Polynomial

theorem rational_charpoly_root_minpoly_degree
    {K I : Type*} [Field K] [CharZero K] [Fintype I] [DecidableEq I]
    (A : Matrix I I ℚ) {z : K}
    (hz : z ∈ (A.map (algebraMap ℚ K)).charpoly.roots) :
    (minpoly ℚ z).natDegree ≤ Fintype.card I := by
  have he : aeval z A.charpoly = 0 := by
    have hh := (mem_roots (A.map (algebraMap ℚ K)).charpoly_monic.ne_zero).mp hz
    rw [Matrix.charpoly_map, IsRoot.def, eval_map, ← aeval_def] at hh
    exact hh
  have hd := natDegree_le_of_dvd (minpoly.dvd ℚ z he) A.charpoly_monic.ne_zero
  simpa only [Matrix.charpoly_natDegree_eq_dim] using hd

theorem rational_torsion_charpoly_root_integral_degree
    {K I : Type*} [Field K] [CharZero K] [Fintype I] [DecidableEq I]
    (A : Matrix I I ℚ) (hA : ∃ m : ℕ, 0 < m ∧ A ^ m = 1) {z : K}
    (hz : z ∈ (A.map (algebraMap ℚ K)).charpoly.roots) :
    (∃ m : ℕ, 0 < m ∧ z ^ m = 1) ∧
      (minpoly ℤ z).natDegree ≤ Fintype.card I := by
  obtain ⟨m, hm, hpow⟩ := hA
  have hp : (A.map (algebraMap ℚ K)) ^ m = 1 := by
    have hh := congrArg (RingHom.mapMatrix (algebraMap ℚ K)) hpow
    simpa only [map_pow, map_one, RingHom.mapMatrix_apply] using hh
  have he := charpoly_root_power_eq_one _ m hp hz
  refine ⟨⟨m, hm, he⟩, ?_⟩
  have hi : IsIntegral ℤ z := IsIntegral.of_pow hm (by rw [he]; exact isIntegral_one)
  have hd := rational_charpoly_root_minpoly_degree A hz
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hi,
    (minpoly.monic hi).natDegree_map] at hd
  exact hd

end PolycyclicRecognition

end

end OAI
