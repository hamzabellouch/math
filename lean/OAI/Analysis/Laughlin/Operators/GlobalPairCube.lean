import OAI.Analysis.Laughlin.Pair.AffineChart
import OAI.Analysis.Laughlin.Spin.PairDecomposition

namespace OAI

namespace Laughlin
open MvPolynomial
open scoped BigOperators

theorem pairAffineChart_coefficient {N Q : ℕ} (ψ : State N Q)
    (i j : Fin N) (hij : i ≠ j) (a : PairSpectators (Q := Q) i j) :
    (pairAffineChart i j (spinPolynomial ψ)).coeff (affineExponent a.val) =
      Polynomial.C (Polynomial.C (spectatorWeight i j a.val)) *
        pairAffinePolynomial Q (pairSlice ψ i j a.val) := by
  classical
  rw [spinPolynomial_pair_decomposition ψ i j hij]
  simp only [map_sum, map_mul]
  simp_rw [pairAffineChart_spectator i j hij, pairAffineChart_pair i j hij]
  simp only [coeff_sum]
  simp_rw [mul_comm (monomial _ _) (C _), coeff_C_mul, coeff_monomial, mul_ite, mul_zero]
  have he (b : PairSpectators (Q := Q) i j) :
      affineExponent b.val = affineExponent a.val ↔ b = a := by
    rw [(affineExponent_injective N Q).eq_iff]
    exact Subtype.val_injective.eq_iff
  simp_rw [he]
  simp [mul_comm]

theorem affine_pair_cubes_of_bracket_dvd {N Q : ℕ} (ψ : State N Q)
    (i j : Fin N) (hij : i ≠ j) (hc : bracket i j^3 ∣ spinPolynomial ψ)
    (a : Configuration N Q) :
    PairDiagonal.diagonal^3 ∣ pairAffinePolynomial Q (pairSlice ψ i j a) := by
  let a0 : PairSpectators (Q := Q) i j :=
    ⟨Function.update (Function.update a i 0) j 0, by simp [hij]⟩
  have hd := map_dvd (pairAffineChart i j) hc
  rw [map_pow, pairAffineChart_bracket i j hij, ← map_pow] at hd
  obtain ⟨g,hg⟩ := hd
  have he : Polynomial.C (Polynomial.C (spectatorWeight i j a0.val)) *
      pairAffinePolynomial Q (pairSlice ψ i j a0.val) =
        PairDiagonal.diagonal^3 * g.coeff (affineExponent a0.val) := by
    rw [← pairAffineChart_coefficient ψ i j hij a0, hg, coeff_C_mul]
  have hunit : Polynomial.C (Polynomial.C (spectatorWeight i j a0.val)) *
      Polynomial.C (Polynomial.C (spectatorWeight i j a0.val)⁻¹) = (1 : PairDiagonal.Poly) := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ (spectatorWeight_ne_zero i j a0.val),
      map_one, map_one]
  have hdiv : PairDiagonal.diagonal^3 ∣
      (Polynomial.C (Polynomial.C (spectatorWeight i j a0.val)) *
        pairAffinePolynomial Q (pairSlice ψ i j a0.val)) *
          Polynomial.C (Polynomial.C (spectatorWeight i j a0.val)⁻¹) :=
    dvd_mul_of_dvd_left ⟨g.coeff (affineExponent a0.val), he⟩ _
  rw [mul_right_comm, hunit, one_mul] at hdiv
  simpa only [a0, pairSlice_anchor] using hdiv

theorem affine_pair_cubes_iff_bracket_dvd {N Q : ℕ} (ψ : State N Q)
    (i j : Fin N) (hij : i ≠ j) :
    (∀ a : Configuration N Q,
      PairDiagonal.diagonal^3 ∣ pairAffinePolynomial Q (pairSlice ψ i j a)) ↔
        bracket i j^3 ∣ spinPolynomial ψ :=
  ⟨bracket_cube_dvd_spinPolynomial_of_slices ψ i j hij,
    fun h => affine_pair_cubes_of_bracket_dvd ψ i j hij h⟩

theorem energy_eq_zero_iff_global_pair_cubes {N Q : ℕ} (hQ : 2 ≤ Q)
    (ψ : State N Q) (hψ : Antisymmetric ψ) :
    energy ψ = 0 ↔ ∀ i j : Fin N, i < j → bracket i j^3 ∣ spinPolynomial ψ := by
  rw [energy_eq_zero_iff_affine_pair_cubes hQ ψ hψ]
  constructor
  · intro h i j hij
    exact (affine_pair_cubes_iff_bracket_dvd ψ i j (ne_of_lt hij)).mp (h i j hij)
  · intro h i j hij
    exact (affine_pair_cubes_iff_bracket_dvd ψ i j (ne_of_lt hij)).mpr (h i j hij)

end Laughlin

end OAI
