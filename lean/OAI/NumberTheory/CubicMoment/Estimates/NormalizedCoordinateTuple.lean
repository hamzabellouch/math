import OAI.NumberTheory.CubicMoment.Estimates.LogDenominatorWeights
import OAI.NumberTheory.CubicMoment.Estimates.CoordinateWeightedTuple
import OAI.NumberTheory.CubicMoment.Estimates.PrimeLogReplacement

namespace OAI

/-! Exact restoration of Λ/log(N) on each original factor. -/
noncomputable section
open scoped BigOperators ContDiff
open Set
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma normalizedVonMangoldt_weight {c Y X : ℝ} (hc : 0 < c)
    (hY0 : 0 < Y) (hY : 1 ≤ Real.log Y) (hlo : Y^c ≤ X) (hhi : X ≤ Y)
    (w : ℝ → ℂ) (hw : ∀ x, x < 1 → w x = 0) (a : Eisenstein) :
    (normalizedVonMangoldt a:ℂ)*w (norm a/X) =
      (1/(Real.log Y:ℂ))*((MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt:ℝ):ℂ)*
        logDenominatorWeight c w (Real.log X/Real.log Y,1/Real.log Y) (norm a/X) := by
  by_cases hx : 1 ≤ norm a/X
  · have hX : 0 < X := (Real.rpow_pos_of_pos hY0 c).trans_le hlo
    rw [logDenominatorWeight_scale hc hY0 hY hlo hhi hx]
    have he : X*(norm a/X) = norm a := by field_simp
    rw [he]
    unfold normalizedVonMangoldt
    push_cast
    have hCY : (Real.log Y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by linarith))
    field_simp
  · have hz := hw _ (lt_of_not_ge hx)
    simp only [hz,mul_zero,logDenominatorWeight]

def primaryNormalizedVonMangoldtTuple (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
    (∏ i, (normalizedVonMangoldt (n i):ℂ)*W i (norm (n i)/X i)*
      (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
        mellinPhase (t i) (norm (n i))))*V ((∏ i, norm (n i))/Y)

lemma primaryNormalizedVonMangoldtTuple_eq {c Y : ℝ} (hc : 0 < c)
    (hY0 : 0 < Y) (hY : 1 ≤ Real.log Y) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ)
    (hWlo : ∀ i x, x < 1 → W i x = 0)
    (hXlo : ∀ i, Y^c ≤ X i) (hXhi : ∀ i, X i ≤ Y) :
    primaryNormalizedVonMangoldtTuple a b q η t W X V Y =
      (1/(Real.log Y:ℂ))^(Fintype.card ι)*
      primaryCoordinateWeightedTuple (fun _ : ι => idealVonMangoldt)
        a b q η t (fun i => logDenominatorWeight c (W i)
          (Real.log (X i)/Real.log Y,1/Real.log Y)) X V Y := by
  unfold primaryNormalizedVonMangoldtTuple primaryCoordinateWeightedTuple primaryTupleCore
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp_rw [normalizedVonMangoldt_weight hc hY0 hY (hXlo _) (hXhi _) _ (hWlo _)]
  have he (i : ι) :
      1/(Real.log Y:ℂ)*((MvPowerSeries.coeff (idealExponentOf (n i)) idealVonMangoldt:ℝ):ℂ)*
        logDenominatorWeight c (W i) (Real.log (X i)/Real.log Y,1/Real.log Y) (norm (n i)/X i)*
        (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
          mellinPhase (t i) (norm (n i))) =
      (1/(Real.log Y:ℂ))*
        (((MvPowerSeries.coeff (idealExponentOf (n i)) idealVonMangoldt:ℝ):ℂ)*
        (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
          mellinPhase (t i) (norm (n i))))*
        logDenominatorWeight c (W i) (Real.log (X i)/Real.log Y,1/Real.log Y) (norm (n i)/X i) := by ring
  simp_rw [he,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
  ring

end CubicFirstMoment

end

end OAI
