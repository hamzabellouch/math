import OAI.NumberTheory.CubicMoment.Estimates.IdealMangoldtPrefix
import OAI.NumberTheory.CubicMoment.Estimates.PrimePowerDivisors

namespace OAI

/-! A direct count of higher prime-ideal powers in the complete norm ball.
The map from a prime base and its exponent is used only for an upper bound. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def higherIdealPrimePowers (X : ℝ) : Finset EisensteinIdealExponent :=
  (fullIdealBall X).filter (fun ν => ∃ p : EisensteinIdealPrime, ∃ j : ℕ,
    2 ≤ j ∧ ν = Finsupp.single p j)

lemma fullIdealBall_card_le {X : ℝ} (hX : 0 ≤ X) :
    ((fullIdealBall X).card:ℝ) ≤ 18*X := by
  apply (Nat.cast_le.mpr (Finset.card_image_le)).trans
  exact nonzeroNormBall_card_le hX

lemma idealPrimePower_exponent_bound {ν : EisensteinIdealExponent} {X : ℝ}
    (hν : ν ∈ fullIdealBall X) (p : EisensteinIdealPrime) :
    ν p ≤ Nat.log 2 ⌊X⌋₊ := by
  have hh := idealExponentOf_le_log_norm (idealExponentGenerator_ne_zero ν) p
  rw [idealExponentOf_generator] at hh
  apply hh.trans
  apply Nat.log_mono_right
  exact Nat.le_floor (mem_fullIdealBall.mp hν)

lemma higherIdealPrimePowers_subset {X : ℝ} (hX : 0 ≤ X) :
    higherIdealPrimePowers X ⊆
      ((fullIdealBall (Real.sqrt X)).product (Finset.range (Nat.log 2 ⌊X⌋₊+1))).image
        (fun v : EisensteinIdealExponent × ℕ => v.2 • v.1) := by
  intro ν hν
  obtain ⟨hball,p,j,hj,rfl⟩ := Finset.mem_filter.mp hν
  have hnorm : (normNat (idealPrimeRepresentative p):ℝ)^j ≤ X := by
    simpa only [mem_fullIdealBall,idealExponentNorm_single] using hball
  have hbase : 1 ≤ (normNat (idealPrimeRepresentative p):ℝ) := by
    exact_mod_cast (show 1 ≤ normNat (idealPrimeRepresentative p) from
      (by have := idealPrimeRepresentative_normNat_ge_two p; omega))
  have hsq : (normNat (idealPrimeRepresentative p):ℝ)^2 ≤ X :=
    (pow_le_pow_right₀ hbase hj).trans hnorm
  have hsmall : Finsupp.single p 1 ∈ fullIdealBall (Real.sqrt X) := by
    rw [mem_fullIdealBall,idealExponentNorm_single,pow_one]
    exact (Real.le_sqrt (by positivity) hX).mpr hsq
  have hlarge := idealPrimePower_exponent_bound hball p
  simp only [Finsupp.single_eq_same] at hlarge
  refine Finset.mem_image.mpr ⟨(Finsupp.single p 1,j),
    Finset.mem_product.mpr ⟨hsmall,Finset.mem_range.mpr (by omega)⟩,?_⟩
  ext q
  by_cases hq : q=p
  · subst q
    simp
  · simp [hq]

theorem higherIdealPrimePowers_card {X : ℝ} (hX : 0 ≤ X) :
    ((higherIdealPrimePowers X).card:ℝ) ≤
      18*Real.sqrt X*(Nat.log 2 ⌊X⌋₊+1) := by
  have hh := Finset.card_le_card (higherIdealPrimePowers_subset hX)
  have hi : ((higherIdealPrimePowers X).card:ℝ) ≤
      (((fullIdealBall (Real.sqrt X)).product
        (Finset.range (Nat.log 2 ⌊X⌋₊+1))).card:ℝ) := by
    exact_mod_cast hh.trans (Finset.card_image_le)
  have hcard : ((fullIdealBall (Real.sqrt X)).product
      (Finset.range (Nat.log 2 ⌊X⌋₊+1))).card =
      (fullIdealBall (Real.sqrt X)).card*(Nat.log 2 ⌊X⌋₊+1) := by
    exact (Finset.card_product _ _).trans (by rw [Finset.card_range])
  rw [hcard,Nat.cast_mul,Nat.cast_add,Nat.cast_one] at hi
  exact hi.trans (mul_le_mul_of_nonneg_right (fullIdealBall_card_le (Real.sqrt_nonneg X)) (by positivity))

theorem higherIdealPrimePowers_mass (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {X : ℝ} (hX : 1 ≤ X) :
    (∑ ν ∈ higherIdealPrimePowers X,
      ‖((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν‖) ≤
      18*Real.sqrt X*(Nat.log 2 ⌊X⌋₊+1)*Real.log X := by
  calc
    _ ≤ ∑ _ν ∈ higherIdealPrimePowers X, Real.log X := by
      apply Finset.sum_le_sum
      intro ν hν
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      calc
        _ ≤ |(MvPowerSeries.coeff ν idealVonMangoldt:ℝ)| :=
          mul_le_of_le_one_right (abs_nonneg _) (hχ ν)
        _ ≤ Real.log (idealExponentNorm ν) := idealVonMangoldt_coeff_abs_le_logNorm ν
        _ ≤ Real.log X := Real.log_le_log (idealExponentNorm_pos ν)
          (mem_fullIdealBall.mp (Finset.mem_filter.mp hν).1)
    _ = ((higherIdealPrimePowers X).card:ℝ)*Real.log X := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (higherIdealPrimePowers_card (by linarith)) (Real.log_nonneg hX)

end CubicFirstMoment

end

end OAI
