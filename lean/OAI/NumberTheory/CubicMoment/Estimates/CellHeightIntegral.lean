import OAI.NumberTheory.CubicMoment.Estimates.FarLogCellHeight

namespace OAI

/-! Finite Fubini for the actual cell polynomials and the height cutoff. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma logCellHeightSum_eq_integral (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (J A B X₀ : ℝ) (e : ℤ × ℤ) (h : ℝ → ℂ) (hi : Integrable h) :
    logCellHeightSum P S α β J A B X₀ e h =
      ∫ t : ℝ, (h t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*
        logCellPolynomial P S α β J A B e t := by
  let Pi := logNormCellSupport P J A e.1
  let Sj := logNormCellSupport S J B e.2
  let c := fun q : Eisenstein × Eisenstein => α q.1*β q.2*gauss (q.1*q.2)
  let n := fun q : Eisenstein × Eisenstein => q.1*q.2
  calc
    _ = ∑ q ∈ Pi.product Sj, c q*heightFourierIntegral h
        (Real.log (norm (n q))-Real.log X₀) := (Finset.sum_product Pi Sj _).symm
    _ = ∫ t : ℝ, (h t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*
        ∑ q ∈ Pi.product Sj, c q*normTwist t (n q) :=
      height_norm_polynomial_integral _ _ _ h hi _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      congr 1
      exact Finset.sum_product Pi Sj _

lemma logCellHeightIntegrand_integrable (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (J A B X₀ : ℝ) (e : ℤ × ℤ) (h : ℝ → ℂ) (hi : Integrable h) :
    Integrable (fun t : ℝ => (h t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*
      logCellPolynomial P S α β J A B e t) := by
  have hw : Integrable (fun t : ℝ => h t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)) :=
    integrable_height_phase h hi (-Real.log X₀)
  let Pi := logNormCellSupport P J A e.1
  let Sj := logNormCellSupport S J B e.2
  let c := fun q : Eisenstein × Eisenstein => α q.1*β q.2*gauss (q.1*q.2)
  apply hw.mul_bdd (c := ∑ q ∈ Pi.product Sj, ‖c q‖)
    (logCellPolynomial_continuous P S α β J A B e).aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  have he : (∑ q ∈ Pi.product Sj, c q*normTwist t (q.1*q.2)) =
      logCellPolynomial P S α β J A B e t := Finset.sum_product Pi Sj _
  rw [←he]
  exact norm_indexed_norm_polynomial (Pi.product Sj) c (fun q => q.1*q.2) t

theorem finite_logCellHeightSum_integral (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (J A B X₀ : ℝ) (E : Finset (ℤ × ℤ)) (h : ℝ → ℂ) (hi : Integrable h) :
    (∑ e ∈ E, logCellHeightSum P S α β J A B X₀ e h) =
      ∫ t : ℝ, (h t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*
        ∑ e ∈ E, logCellPolynomial P S α β J A B e t := by
  simp_rw [logCellHeightSum_eq_integral P S α β J A B X₀ _ h hi]
  rw [←integral_finsetSum E (fun e _ =>
    logCellHeightIntegrand_integrable P S α β J A B X₀ e h hi)]
  apply integral_congr_ae
  filter_upwards with t
  rw [Finset.mul_sum]

end CubicFirstMoment

end

end OAI
