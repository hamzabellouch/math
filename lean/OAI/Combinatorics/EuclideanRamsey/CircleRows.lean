import OAI.Combinatorics.EuclideanRamsey.CircleInterpolation
import Mathlib.LinearAlgebra.LinearIndependent.Defs

namespace OAI
noncomputable section
namespace EuclideanRamsey.CircleConsequence

abbrev QIndex := Option (Fin 2) × Option (Fin 2)
def quadraticRow (a : Fin 5 → Space 2) (i : Fin 5) (q : QIndex) : Coeff a :=
  augmented a i q.1 * augmented a i q.2

/-- Normalized coefficients for quadratic interpolation at five circle points. -/
theorem normalized_isolators (a : Fin 5 → Space 2) (ha : Function.Injective a)
    (c : Space 2) (r : ℝ) (hc : ∀ i, dist (a i) c = r) :
    ∃ L : Fin 5 → QIndex → Coeff a,
      ∀ i j, ∑ q, L i q * quadraticRow a j q = if j = i then 1 else 0 := by
  classical
  have hcoord := circle_coordinates a c r hc
  have hiso (i : Fin 5) : ∃ M : QIndex → Coeff a,
      (∀ j, j ≠ i → ∑ q, M q * quadraticRow a j q = 0) ∧
      (∑ q, M q * quadraticRow a i q) ≠ 0 := by
    obtain ⟨M, hM, hMi⟩ := five_point_isolator a ha c (r^2) hcoord (Equiv.swap 0 i)
    refine ⟨fun q => M q.1 q.2, ?_, ?_⟩
    · intro j hj
      simpa [quadraticRow, Fintype.sum_prod_type, mul_assoc] using hM j (by simpa using hj)
    · simpa [quadraticRow, Fintype.sum_prod_type, mul_assoc] using hMi
  choose M hM hMi using hiso
  refine ⟨fun i q => (∑ t, M i t * quadraticRow a i t)⁻¹ * M i q, ?_⟩
  intro i j
  simp_rw [mul_assoc, ← Finset.mul_sum]
  by_cases hji : j = i
  · subst j
    simp [hMi]
  · simp [hji, hM i j hji]

/-- A concrete right inverse to quadratic evaluation. -/
theorem quadratic_evaluation_surjective (a : Fin 5 → Space 2)
    (ha : Function.Injective a) (c : Space 2) (r : ℝ)
    (hc : ∀ i, dist (a i) c = r) :
    ∀ values : Fin 5 → Coeff a, ∃ coeff : QIndex → Coeff a,
      ∀ j, ∑ q, coeff q * quadraticRow a j q = values j := by
  classical
  obtain ⟨L, hL⟩ := normalized_isolators a ha c r hc
  intro values
  refine ⟨fun q => ∑ i, values i * L i q, ?_⟩
  intro j
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, hL]
  simp

/-- The quadratic evaluation rows are independent because their dual rows isolate them. -/
theorem circle_five_rows_independent (a : Fin 5 → Space 2)
    (ha : Function.Injective a) (c : Space 2) (r : ℝ)
    (hc : ∀ i, dist (a i) c = r) :
    LinearIndependent (Coeff a) (fun i : Fin 5 => fun q : QIndex =>
      augmented a i q.1 * augmented a i q.2) := by
  classical
  obtain ⟨L, hL⟩ := normalized_isolators a ha c r hc
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hzero (q : QIndex) : ∑ j, g j * quadraticRow a j q = 0 := by
    simpa [quadraticRow] using congrFun hg q
  have hpair : ∑ q, L i q * (∑ j, g j * quadraticRow a j q) = 0 := by
    simp [hzero]
  have hcalc : (∑ q, L i q * (∑ j, g j * quadraticRow a j q)) = g i := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ j, g j * (∑ q, L i q * quadraticRow a j q) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ = g i := by simp [hL]
  exact hcalc.symm.trans hpair
end EuclideanRamsey.CircleConsequence

end

end OAI
