import OAI.NumberTheory.CubicMoment.Estimates.WideLogDenominator
import OAI.NumberTheory.CubicMoment.Angular.AngularNormalizedCoordinateMoments

namespace OAI

noncomputable section
open Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primaryAngularNormalizedVonMangoldtTuple_eq_lower {c Y : ℝ} (hc : 0 < c)
    (hY0 : 0 < Y) (hY : 1 ≤ Real.log Y) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ)
    (hWlo : ∀ i x, x < 1 → W i x = 0)
    (hXlo : ∀ i, Y^c ≤ X i) :
    primaryAngularNormalizedVonMangoldtTuple ℓ a b q η t W X V Y =
      (1/(Real.log Y:ℂ))^(Fintype.card ι)*
      primaryAngularCoordinateWeightedTuple ℓ (fun _ : ι => idealVonMangoldt)
        a b q η t (fun i => logDenominatorWeight c (W i)
          (Real.log (X i)/Real.log Y,1/Real.log Y)) X V Y := by
  unfold primaryAngularNormalizedVonMangoldtTuple primaryAngularCoefficientTuple primaryAngularCoordinateWeightedTuple primaryAngularTupleCore
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp_rw [normalizedVonMangoldt_weight_lower hc hY0 hY (hXlo _) _ (hWlo _)]
  have he (i : ι) :
      1/(Real.log Y:ℂ)*((MvPowerSeries.coeff (idealExponentOf (n i)) idealVonMangoldt:ℝ):ℂ)*
        logDenominatorWeight c (W i) (Real.log (X i)/Real.log Y,1/Real.log Y) (norm (n i)/X i)*
        (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*theta ℓ (n i)*
          mellinPhase (t i) (norm (n i))) =
      (1/(Real.log Y:ℂ))*
        (((MvPowerSeries.coeff (idealExponentOf (n i)) idealVonMangoldt:ℝ):ℂ)*
        (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*theta ℓ (n i)*
          mellinPhase (t i) (norm (n i))))*
        logDenominatorWeight c (W i) (Real.log (X i)/Real.log Y,1/Real.log Y) (norm (n i)/X i) := by ring
  simp_rw [he,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
  ring

lemma angular_normalizedCoordinate_norm_le_lower {c Y : ℝ} (hc : 0 < c) (hY0 : 0 < Y)
    (hY : 1 ≤ Real.log Y) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ)
    (hWlo : ∀ i x, x < 1 → W i x = 0)
    (hXlo : ∀ i, Y^c ≤ X i) :
    ‖primaryAngularNormalizedVonMangoldtTuple ℓ a b q η t W X V Y‖ ≤
      ‖primaryAngularCoordinateWeightedTuple ℓ (fun _ : ι => idealVonMangoldt)
        a b q η t (fun i => logDenominatorWeight c (W i)
          (Real.log (X i)/Real.log Y,1/Real.log Y)) X V Y‖ := by
  rw [primaryAngularNormalizedVonMangoldtTuple_eq_lower ℓ hc hY0 hY a b q η t W X V hWlo hXlo,
    norm_mul,norm_pow]
  apply mul_le_of_le_one_left (_root_.norm_nonneg _)
  apply pow_le_one₀ (_root_.norm_nonneg _) _
  rw [norm_div,norm_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith)]
  exact (div_le_one (by linarith)).mpr hY

end CubicFirstMoment

end

end OAI
