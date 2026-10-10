import OAI.NumberTheory.CubicMoment.Estimates.LogDenominatorWeights
import OAI.NumberTheory.CubicMoment.Angular.AngularCoordinateWeightedTuple
import OAI.NumberTheory.CubicMoment.Angular.AngularPrimeCoordinateCollection
import OAI.NumberTheory.CubicMoment.Estimates.NormalizedCoordinateTuple
import OAI.NumberTheory.CubicMoment.Estimates.PrimeLogReplacement

namespace OAI

/-! Exact restoration of Λ/log(N) on each original factor. -/
noncomputable section
open scoped BigOperators ContDiff
open Set
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primaryAngularNormalizedVonMangoldtTuple (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  primaryAngularCoefficientTuple ℓ (fun n => (normalizedVonMangoldt n:ℂ)) a b q η t W X V Y

lemma primaryAngularNormalizedVonMangoldtTuple_eq {c Y : ℝ} (hc : 0 < c)
    (hY0 : 0 < Y) (hY : 1 ≤ Real.log Y) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ)
    (hWlo : ∀ i x, x < 1 → W i x = 0)
    (hXlo : ∀ i, Y^c ≤ X i) (hXhi : ∀ i, X i ≤ Y) :
    primaryAngularNormalizedVonMangoldtTuple ℓ a b q η t W X V Y =
      (1/(Real.log Y:ℂ))^(Fintype.card ι)*
      primaryAngularCoordinateWeightedTuple ℓ (fun _ : ι => idealVonMangoldt)
        a b q η t (fun i => logDenominatorWeight c (W i)
          (Real.log (X i)/Real.log Y,1/Real.log Y)) X V Y := by
  unfold primaryAngularNormalizedVonMangoldtTuple primaryAngularCoefficientTuple primaryAngularCoordinateWeightedTuple primaryAngularTupleCore
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp_rw [normalizedVonMangoldt_weight hc hY0 hY (hXlo _) (hXhi _) _ (hWlo _)]
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

end CubicFirstMoment

end

end OAI
