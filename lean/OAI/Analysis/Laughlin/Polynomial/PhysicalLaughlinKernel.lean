import OAI.Analysis.Laughlin.Operators.GlobalPairCube
import OAI.Analysis.Laughlin.Polynomial.LaughlinAntisymmetry

namespace OAI

namespace Laughlin
open MvPolynomial
open scoped BigOperators

theorem spinPolynomial_scalar {N Q : ℕ} (c : ℂ) (ψ : State N Q) :
    spinPolynomial (fun a => c * ψ a) = C c * spinPolynomial ψ := by
  unfold spinPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [C_mul_monomial]
  congr 1
  ring

theorem physical_Laughlin_kernel {N : ℕ} (hN : 2 ≤ N)
    (ψ : State N (3*(N-1))) (hψ : Antisymmetric ψ) :
    energy ψ = 0 ↔ ∃ c : ℂ, ψ = fun a => c * laughlinVector N (3*(N-1)) a := by
  constructor
  · exact zero_energy_state_eq_laughlin hN ψ hψ
  · rintro ⟨c,hc⟩
    apply (energy_eq_zero_iff_global_pair_cubes (by omega) ψ hψ).mpr
    intro i j hij
    rw [hc, spinPolynomial_scalar, spinPolynomial_laughlinVector]
    exact dvd_mul_of_dvd_right (bracket_cube_dvd_laughlin hij) _

theorem laughlinVector_zero_energy {N : ℕ} (hN : 2 ≤ N) :
    energy (laughlinVector N (3*(N-1))) = 0 := by
  apply (physical_Laughlin_kernel hN _ (laughlinVector_antisymmetric N)).mpr
  exact ⟨1, by funext a; simp⟩

theorem physical_Laughlin_ground_line {N : ℕ} (hN : 2 ≤ N) :
    laughlinVector N (3*(N-1)) ≠ 0 ∧
    Antisymmetric (laughlinVector N (3*(N-1))) ∧
    energy (laughlinVector N (3*(N-1))) = 0 ∧
    ∀ ψ : State N (3*(N-1)), Antisymmetric ψ →
      (energy ψ = 0 ↔ ∃ c : ℂ, ψ = fun a => c * laughlinVector N (3*(N-1)) a) :=
  ⟨laughlinVector_ne_zero N, laughlinVector_antisymmetric N,
    laughlinVector_zero_energy hN, fun ψ hψ => physical_Laughlin_kernel hN ψ hψ⟩

end Laughlin

end OAI
