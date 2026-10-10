import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.OrbitalCutoffTail
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.WellFieldOrbitalResidual

namespace OAI

/-! The finite vertical cutoff error after retaining the intended well-depth
counterterms. Its bound decays with the slab height and does not include the
counterterm itself as an error. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem countertermWellSum_abs_bound (freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) {δ : ℝ}
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (r : PlanarPosition) :
    |countertermWellSum freq scale u r| ≤ (m:ℝ)*(δ+1)*PlanarSobolev.wellBound := by
  have h := (abs_add_le (countertermWellSum freq scale u r-planarWellSum u r) (planarWellSum u r)).trans
    (add_le_add (countertermWellSum_sub_abs_bound freq scale u hcoeff r) (planarWellSum_abs_bound u r))
  rw [sub_add_cancel] at h
  convert h using 1
  ring

def finiteWellOrbitalResidual (freq scale S : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) (x : Position) : ℝ :=
  (manufacturedWellField freq scale S u x-countertermWellSum freq scale u (positionSplitCoordinates x).1)*
    continuumLocalizedMode freq (u j) x

theorem finiteWellOrbitalResidual_continuous (freq scale S : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (j : Fin m) :
    Continuous (finiteWellOrbitalResidual freq scale S u j) :=
  ((manufacturedWellField_C7 freq scale S u).continuous.sub
    ((countertermWellSum_C7 freq scale u).continuous.comp positionSplitCoordinates.continuous.fst)).mul
      (continuumLocalizedMode_C7 freq (u j)).continuous

theorem finiteWellOrbitalResidual_square_bound {freq S : ℝ} (hfreq : 0 < freq) (hS : 0 < S)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ δ) (j : Fin m) :
    Integrable (fun x => finiteWellOrbitalResidual freq scale S u j x^2) ∧
    (∫ x, finiteWellOrbitalResidual freq scale S u j x^2) ≤
      ((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2/(S/2)^24*
        (∫ x, ‖x‖^24*continuumLocalizedMode freq 0 x^2) := by
  let a : Position → ℝ := fun x => manufacturedWellField freq scale S u x-
    countertermWellSum freq scale u (positionSplitCoordinates x).1
  let B := (m:ℝ)*(δ+1)*PlanarSobolev.wellBound
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (by linarith))
    PlanarSobolev.wellBound_nonnegative
  have ha : Continuous a := (manufacturedWellField_C7 freq scale S u).continuous.sub
    ((countertermWellSum_C7 freq scale u).continuous.comp positionSplitCoordinates.continuous.fst)
  have hb (x : Position) : |a x| ≤ B := by
    have ht := slabWellCutoff_bounds S (positionSplitCoordinates x).2
    have ht' : |slabWellCutoff S (positionSplitCoordinates x).2-1| ≤ 1 := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    change |slabWellCutoff S (positionSplitCoordinates x).2*
      countertermWellSum freq scale u (positionSplitCoordinates x).1-
      countertermWellSum freq scale u (positionSplitCoordinates x).1| ≤ B
    rw [← sub_one_mul,abs_mul]
    exact (mul_le_mul_of_nonneg_right ht' (abs_nonneg _)).trans
      (by simpa only [one_mul] using countertermWellSum_abs_bound freq scale u hcoeff (positionSplitCoordinates x).1)
  have hz (x : Position) (hx : ‖x-planarCenter (u j)‖ < S/2) : a x = 0 := by
    have hcenter : planarCenter (u j) 2 = 0 := by
      simpa only [planarCenter,ContinuousLinearEquiv.apply_symm_apply] using
        (positionSplitCoordinates_snd (planarCenter (u j))).symm
    have hcoord := (PiLp.norm_apply_le (x-planarCenter (u j)) 2).trans hx.le
    have hcoord' : |(positionSplitCoordinates x).2| ≤ S/2 := by
      simpa only [positionSplitCoordinates_snd,PiLp.sub_apply,hcenter,sub_zero,Real.norm_eq_abs] using hcoord
    exact sub_eq_zero.mpr (manufacturedWellField_inner freq scale hS u x hcoord')
  have h := localized_weighted_coefficient_tail (half_pos hS) hB (planarCenter (u j)) ha
    (continuumLocalizedMode_C7 freq (u j)).continuous hb hz
    (continuumLocalizedMode_centered_twentyFourth_moment_integrable hfreq (u j))
  refine ⟨h.1,?_⟩
  apply h.2.trans_eq
  simp_rw [continuumLocalizedMode_translate freq (u j)]
  rw [integral_sub_right_eq_self (μ := volume)
    (fun x : Position => ‖x‖^24*continuumLocalizedMode freq 0 x^2) (planarCenter (u j))]

end ContinuumCoulomb

end

end OAI
