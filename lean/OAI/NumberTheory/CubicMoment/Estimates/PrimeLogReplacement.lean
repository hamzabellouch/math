import OAI.NumberTheory.CubicMoment.Estimates.IdealVonMangoldt
import OAI.NumberTheory.CubicMoment.Estimates.PrimePowerSupport

namespace OAI

/-! Exact replacement of a prime indicator by von Mangoldt divided by log norm.
The discrepancy is bounded and is supported on actual higher primary prime powers. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def normalizedVonMangoldt (a : Eisenstein) : ℝ :=
  MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt / Real.log (norm a)

def primeIndicator (a : Eisenstein) : ℝ := if Prime a then 1 else 0

def primeLogCorrection (a : Eisenstein) : ℝ :=
  normalizedVonMangoldt a-primeIndicator a

lemma prime_norm_gt_one {p : Eisenstein} (hp : Prime p) : 1 < norm p := by
  have hn := one_le_norm hp.ne_zero
  apply lt_of_le_of_ne hn
  intro he
  exact hp.not_isUnit (isUnit_of_norm_eq_one he.symm)

lemma normalizedVonMangoldt_at_prime {p : Eisenstein} (hp : Prime p) :
    normalizedVonMangoldt p = 1 := by
  rw [normalizedVonMangoldt,idealVonMangoldt_at_prime hp]
  exact div_self (Real.log_pos (prime_norm_gt_one hp)).ne'

lemma normalizedVonMangoldt_nonneg {a : Eisenstein} (ha : primary a) :
    0 ≤ normalizedVonMangoldt a :=
  div_nonneg (idealVonMangoldt_coeff_nonneg _)
    (Real.log_nonneg (one_le_norm (primary_ne_zero ha)))

lemma normalizedVonMangoldt_le_one {a : Eisenstein} (ha : primary a) :
    normalizedVonMangoldt a ≤ 1 := by
  have hlog : 0 ≤ Real.log (norm a) := Real.log_nonneg (one_le_norm (primary_ne_zero ha))
  have hΛ : MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt ≤ Real.log (norm a) := by
    simpa only [idealExponentOf_norm (primary_ne_zero ha)] using
      idealVonMangoldt_coeff_le_logNorm (idealExponentOf a)
  by_cases hz : Real.log (norm a) = 0
  · simp only [normalizedVonMangoldt,hz,div_zero]
    norm_num
  · exact (div_le_one (lt_of_le_of_ne hlog (Ne.symm hz))).mpr hΛ

lemma primeLogCorrection_at_prime {p : Eisenstein} (hp : Prime p) :
    primeLogCorrection p = 0 := by
  simp only [primeLogCorrection,normalizedVonMangoldt_at_prime hp,primeIndicator,
    ite_eq_left hp,sub_self]

lemma primeLogCorrection_bounds {a : Eisenstein} (ha : primary a) :
    0 ≤ primeLogCorrection a ∧ primeLogCorrection a ≤ 1 := by
  by_cases hp : Prime a
  · rw [primeLogCorrection_at_prime hp]
    norm_num
  · simp only [primeLogCorrection,primeIndicator,ite_eq_right hp,sub_zero]
    exact ⟨normalizedVonMangoldt_nonneg ha,normalizedVonMangoldt_le_one ha⟩

lemma primeIndicator_eq_normalized_sub_correction (a : Eisenstein) :
    primeIndicator a = normalizedVonMangoldt a-primeLogCorrection a := by
  unfold primeLogCorrection
  ring

lemma primeLogCorrection_support {a : Eisenstein} (ha : primary a)
    (he : primeLogCorrection a ≠ 0) :
    ∃ p : Eisenstein, ∃ j : ℕ, primaryPrime p ∧ 2 ≤ j ∧ a = p^j := by
  have hp : ¬ Prime a := fun hp => he (primeLogCorrection_at_prime hp)
  have hΛ : MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt ≠ 0 := by
    intro hz
    apply he
    simp only [primeLogCorrection,primeIndicator,ite_eq_right hp,normalizedVonMangoldt,hz,
      zero_div,sub_self]
  exact idealVonMangoldt_primary_nonprime_support ha hp hΛ

lemma primeLogCorrection_mem_largePrimePowerSupport {a : Eisenstein} (ha : primary a)
    (he : primeLogCorrection a ≠ 0) {Y c : ℝ}
    (hlarge : Y^c < norm a) (hsmall : norm a ≤ Y) :
    a ∈ largePrimePowerSupport Y c := by
  obtain ⟨p,j,hp,hj,heq⟩ := primeLogCorrection_support ha he
  apply Finset.mem_filter.mpr
  refine ⟨mem_nonzeroNormBall.mpr ⟨hsmall,primary_ne_zero ha⟩,p,j,hp,hj,?_,?_⟩
  · rwa [← heq]
  · rw [← heq]

end CubicFirstMoment

end

end OAI
