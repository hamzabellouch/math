import OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope

namespace OAI

namespace PiExponentJets.W64

open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k] [Finite σ]

noncomputable def colonHilbertNumerator (P : ℕ → Polynomial ℤ) (m : ℕ) : Polynomial ℤ :=
  (∑ j ∈ Finset.range m, Polynomial.X ^ j * P j) * (1 - Polynomial.X) +
    Polynomial.X ^ m * P m

theorem stabilized_colon_polynomial_numerator
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (f : MvPolynomial σ k) (hf : f.IsHomogeneous 1) (m r : ℕ)
    (hstable : iteratedColon I f (m+1) = iteratedColon I f m)
    (P : ℕ → Polynomial ℤ)
    (hP : ∀ j : ℕ, sectionHilbertSeries (Ideal.span {f} ⊔ iteratedColon I f j) =
      (P j : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ r).val) :
    sectionHilbertSeries I = (colonHilbertNumerator P m : PowerSeries ℤ) *
      (PowerSeries.invOneSubPow ℤ (r+1)).val := by
  have hu : (PowerSeries.invOneSubPow ℤ r).val =
      (1-PowerSeries.X) * (PowerSeries.invOneSubPow ℤ (r+1)).val := by
    symm
    simpa only [pow_one, Nat.add_comm] using
      PowerSeries.one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val ℤ r 1
  have hv : (PowerSeries.invOneSubPow ℤ r).val * (PowerSeries.invOneSubPow ℤ 1).val =
      (PowerSeries.invOneSubPow ℤ (r+1)).val := by
    rw [← Units.val_mul, ← PowerSeries.invOneSubPow_add]
  rw [stabilized_iteratedColon_series I hI f hf m hstable]
  simp_rw [hP]
  have hsum : (∑ j ∈ Finset.range m,
      PowerSeries.X ^ j * ((P j : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ r).val)) =
      (∑ j ∈ Finset.range m, PowerSeries.X ^ j * (P j : PowerSeries ℤ)) *
        (PowerSeries.invOneSubPow ℤ r).val := by
    simp only [Finset.sum_mul, mul_assoc]
  rw [hsum, mul_assoc (P m : PowerSeries ℤ), hv, hu]
  have hcoe : (colonHilbertNumerator P m : PowerSeries ℤ) =
      (∑ j ∈ Finset.range m, PowerSeries.X ^ j * (P j : PowerSeries ℤ)) *
        (1-PowerSeries.X) + PowerSeries.X ^ m * (P m : PowerSeries ℤ) := by
    change Polynomial.coeToPowerSeries.ringHom
      ((∑ j ∈ Finset.range m, Polynomial.X ^ j * P j) * (1-Polynomial.X) +
        Polynomial.X ^ m * P m) = _
    rw [map_add, map_mul, map_sum]
    simp only [map_mul, map_sub, map_pow, map_one]
    simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
  rw [hcoe]
  ring

end PiExponentJets.W64

end OAI
