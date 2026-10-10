import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedMomentTail
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedWellField

namespace OAI

/-! The cutoff and depth-counterterm contribution to the actual localized
one-particle residual. The estimate uses polynomially many spatial modes. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planarWellSum_abs_bound {m : ℕ} (u : Fin m → PlanarPosition) (r : PlanarPosition) :
    |planarWellSum u r| ≤ (m : ℝ)*PlanarSobolev.wellBound := by
  unfold planarWellSum
  calc
    _ ≤ ∑ i, |manufacturedPlanarWell (r-u i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, PlanarSobolev.wellBound := Finset.sum_le_sum (fun i _ => by
      simpa only [Real.norm_eq_abs] using PlanarSobolev.wellBound_spec (r-u i))
    _ = _ := by simp

theorem countertermWellSum_sub_eq (freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (r : PlanarPosition) :
    countertermWellSum freq scale u r-planarWellSum u r =
      ∑ i, (localizedCounterterm freq u i/scale)*manufacturedPlanarWell (r-u i) := by
  unfold countertermWellSum planarWellSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem countertermWellSum_sub_abs_bound (freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) {δ : ℝ}
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (r : PlanarPosition) :
    |countertermWellSum freq scale u r-planarWellSum u r| ≤
      (m : ℝ)*δ*PlanarSobolev.wellBound := by
  rw [countertermWellSum_sub_eq]
  calc
    _ ≤ ∑ i, |(localizedCounterterm freq u i/scale)*manufacturedPlanarWell (r-u i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, δ*PlanarSobolev.wellBound := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hcoeff i).1]
      exact mul_le_mul (hcoeff i).2 (by
        simpa only [Real.norm_eq_abs] using PlanarSobolev.wellBound_spec (r-u i))
        (abs_nonneg _) ((hcoeff i).1.trans (hcoeff i).2)
    _ = _ := by simp [mul_assoc]

theorem manufacturedWellField_sub_abs_bound (freq scale S : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) {δ : ℝ} (_hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (x : Position) :
    |manufacturedWellField freq scale S u x-planarWellSum u (positionSplitCoordinates x).1| ≤
      (m : ℝ)*(δ+1)*PlanarSobolev.wellBound := by
  let t := slabWellCutoff S (positionSplitCoordinates x).2
  let a := countertermWellSum freq scale u (positionSplitCoordinates x).1
  let b := planarWellSum u (positionSplitCoordinates x).1
  have ht : 0 ≤ t ∧ t ≤ 1 := slabWellCutoff_bounds _ _
  have hdiff := countertermWellSum_sub_abs_bound freq scale u hcoeff (positionSplitCoordinates x).1
  have hb := planarWellSum_abs_bound u (positionSplitCoordinates x).1
  have h1 : |t-1| ≤ 1 := by rw [abs_of_nonpos (by linarith : t-1 ≤ 0)]; linarith
  have he : t*a-b = t*(a-b)+(t-1)*b := by ring
  change |t*a-b| ≤ _
  rw [he]
  calc
    _ ≤ |t*(a-b)|+|(t-1)*b| := abs_add_le _ _
    _ ≤ (m : ℝ)*δ*PlanarSobolev.wellBound+(m : ℝ)*PlanarSobolev.wellBound := by
      rw [abs_mul, abs_mul, abs_of_nonneg ht.1]
      exact add_le_add
        ((mul_le_mul_of_nonneg_right ht.2 (abs_nonneg _)).trans (by simpa only [one_mul] using hdiff))
        ((mul_le_mul_of_nonneg_right h1 (abs_nonneg _)).trans (by simpa only [one_mul] using hb))
    _ = _ := by ring

def wellFieldOrbitalResidual (freq scale S : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) (x : Position) : ℝ :=
  (manufacturedWellField freq scale S u x-planarWellSum u (positionSplitCoordinates x).1)*
    continuumLocalizedMode freq (u j) x

theorem wellFieldOrbitalResidual_square_integrable {freq : ℝ} (hfreq : 0 < freq)
    (scale S : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (j : Fin m) :
    Integrable (fun x => wellFieldOrbitalResidual freq scale S u j x^2) := by
  have hm : MemLp (wellFieldOrbitalResidual freq scale S u j) 2 := by
    apply (continuumLocalizedMode_memLp hfreq (u j)).of_le_mul
      (c := (m : ℝ)*(δ+1)*PlanarSobolev.wellBound)
      ((((manufacturedWellField_C7 freq scale S u).continuous.sub
        ((planarWellSum_continuous u).comp positionSplitCoordinates.continuous.fst)).mul
        (continuumLocalizedMode_C7 freq (u j)).continuous).aestronglyMeasurable)
    filter_upwards [] with x
    change ‖(manufacturedWellField freq scale S u x-planarWellSum u (positionSplitCoordinates x).1)*
      continuumLocalizedMode freq (u j) x‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (manufacturedWellField_sub_abs_bound freq scale S u hδ hcoeff x)
      (norm_nonneg _)
  exact hm.integrable_sq

theorem wellFieldOrbitalResidual_square_bound {freq S : ℝ} (hfreq : 0 < freq)
    (hS : 0 < S) (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (j : Fin m) :
    (∫ x, wellFieldOrbitalResidual freq scale S u j x^2) ≤
      ((m : ℝ)*δ*PlanarSobolev.wellBound)^2+
      ((m : ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*
        (localizedDensityMoment freq (u j) 8/(S/2)^8) := by
  let K := Metric.closedBall (0 : Position) (S/2)
  let A := (m : ℝ)*δ*PlanarSobolev.wellBound
  let B := (m : ℝ)*(δ+1)*PlanarSobolev.wellBound
  have hK : MeasurableSet K := Metric.isClosed_closedBall.measurableSet
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (Nat.cast_nonneg m) hδ) PlanarSobolev.wellBound_nonnegative
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (by linarith)) PlanarSobolev.wellBound_nonnegative
  have hi := wellFieldOrbitalResidual_square_integrable hfreq scale S u hδ hcoeff j
  have hd := localizedDensity_integrable hfreq (u j)
  have hp (x : Position) (hx : x ∈ K) : wellFieldOrbitalResidual freq scale S u j x^2 ≤
      A^2*localizedDensity freq (u j) x := by
    have hxnorm : ‖x‖ ≤ S/2 := by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hx
    have hz : |(positionSplitCoordinates x).2| ≤ S/2 := by
      simpa only [positionSplitCoordinates_snd, Real.norm_eq_abs] using
        (PiLp.norm_apply_le x 2).trans hxnorm
    have hb := countertermWellSum_sub_abs_bound freq scale u hcoeff (positionSplitCoordinates x).1
    rw [← manufacturedWellField_inner freq scale hS u x hz] at hb
    have h := mul_le_mul_of_nonneg_right ((sq_le_sq₀ (abs_nonneg _) hA).mpr hb)
      (localizedDensity_nonnegative freq (u j) x)
    simpa only [wellFieldOrbitalResidual, localizedDensity, mul_pow, sq_abs] using h
  have hq (x : Position) : wellFieldOrbitalResidual freq scale S u j x^2 ≤
      B^2*localizedDensity freq (u j) x := by
    have hb := manufacturedWellField_sub_abs_bound freq scale S u hδ hcoeff x
    have h := mul_le_mul_of_nonneg_right ((sq_le_sq₀ (abs_nonneg _) hB).mpr hb)
      (localizedDensity_nonnegative freq (u j) x)
    simpa only [wellFieldOrbitalResidual, localizedDensity, mul_pow, sq_abs] using h
  have hin := setIntegral_mono_on hi.integrableOn (hd.const_mul (A^2)).integrableOn hK hp
  have hout := setIntegral_mono_on hi.integrableOn (hd.const_mul (B^2)).integrableOn hK.compl
    (fun x _ => hq x)
  rw [integral_const_mul] at hin hout
  have hmass : (∫ x in K, localizedDensity freq (u j) x) ≤ 1 := by
    rw [← localizedDensity_mass hfreq (u j)]
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (localizedDensity_nonnegative freq (u j))) hd
  have htail := localizedDensity_mass_tail_eighth hfreq (half_pos hS) (u j) hK
    (fun x hx => (lt_of_not_ge (by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hx)).le)
  have h := add_le_add (hin.trans (mul_le_mul_of_nonneg_left hmass (sq_nonneg A)))
    (hout.trans (mul_le_mul_of_nonneg_left htail (sq_nonneg B)))
  rw [integral_add_compl hK hi] at h
  simpa only [mul_one, A, B] using h

end ContinuumCoulomb

end

end OAI
