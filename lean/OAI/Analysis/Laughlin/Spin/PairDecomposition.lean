import OAI.Analysis.Laughlin.Pair.SpinorCube
import OAI.Analysis.Laughlin.Spin.OrbitalExpansion
import OAI.Analysis.Laughlin.Spin.PolynomialDegree

namespace OAI

namespace Laughlin
open MvPolynomial
open scoped BigOperators

theorem pairSpinorPolynomial_orbitals {N Q : ℕ} (i j : Fin N)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) :
    pairSpinorPolynomial C (X (i,false)) (X (i,true)) (X (j,false)) (X (j,true)) Q ψ =
      ∑ x, ∑ y, C (ψ x y) * spinOrbitalPolynomial Q i x * spinOrbitalPolynomial Q j y := by
  unfold pairSpinorPolynomial
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  simp only [weightedPairCoordinate, Complex.ofReal_mul, map_mul, spinOrbitalPolynomial]
  ring

theorem spinPolynomial_pair_decomposition {N Q : ℕ} (ψ : State N Q)
    (i j : Fin N) (hij : i ≠ j) :
    spinPolynomial ψ = ∑ a : PairSpectators (Q := Q) i j,
      spectatorPolynomial i j a.val *
      pairSpinorPolynomial C (X (i,false)) (X (i,true)) (X (j,false)) (X (j,true)) Q
        (pairSlice ψ i j a.val) := by
  rw [spinPolynomial_expansion, sum_pair_configurations i j hij]
  apply Finset.sum_congr rfl
  intro a ha
  rw [pairSpinorPolynomial_orbitals]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [spinOrbital_update_product i j hij]
  unfold pairSlice
  ring

theorem bracket_cube_dvd_spinPolynomial_of_slices {N Q : ℕ} (ψ : State N Q)
    (i j : Fin N) (hij : i ≠ j)
    (hc : ∀ a : Configuration N Q,
      PairDiagonal.diagonal^3 ∣ pairAffinePolynomial Q (pairSlice ψ i j a)) :
    bracket i j^3 ∣ spinPolynomial ψ := by
  rw [spinPolynomial_pair_decomposition ψ i j hij]
  apply Finset.dvd_sum
  intro a ha
  exact dvd_mul_of_dvd_right (pairSpinorPolynomial_bracket_cube i j _ (hc a.val)) _

theorem energy_zero_global_pair_cubes {N Q : ℕ} (hQ : 2 ≤ Q)
    (ψ : State N Q) (hψ : Antisymmetric ψ) (hE : energy ψ = 0) :
    ∀ i j : Fin N, i < j → bracket i j^3 ∣ spinPolynomial ψ := by
  intro i j hij
  exact bracket_cube_dvd_spinPolynomial_of_slices ψ i j (ne_of_lt hij)
    ((energy_eq_zero_iff_affine_pair_cubes hQ ψ hψ).mp hE i j hij)

theorem zero_energy_state_eq_laughlin {N : ℕ} (hN : 2 ≤ N)
    (ψ : State N (3*(N-1))) (hψ : Antisymmetric ψ) (hE : energy ψ = 0) :
    ∃ c : ℂ, ψ = fun a => c * laughlinVector N (3*(N-1)) a := by
  exact state_eq_laughlin_of_pair_cubes ψ
    (energy_zero_global_pair_cubes (by omega) ψ hψ hE)

end Laughlin

end OAI
