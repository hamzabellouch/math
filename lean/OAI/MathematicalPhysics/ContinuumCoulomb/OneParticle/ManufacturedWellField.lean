import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.VerticalCappedForm
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarWellLocalization
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedCounterterms
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarSobolev
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.DensitySynthesis

namespace OAI

/-! The actual compact three-dimensional well field in the unit-charge
construction. Its coefficients are Coulomb counterterms. The cutoff only weakens the attractive uncorrected wells. -/

noncomputable section
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

def slabWellCutoff (S z : ℝ) : ℝ := verticalCutoffBump ((2/S)*z)

theorem slabWellCutoff_bounds (S z : ℝ) :
    0 ≤ slabWellCutoff S z ∧ slabWellCutoff S z ≤ 1 :=
  ⟨verticalCutoffBump.nonneg, verticalCutoffBump.le_one⟩

theorem slabWellCutoff_smooth (S : ℝ) : ContDiff ℝ ∞ (slabWellCutoff S) :=
  verticalCutoffBump.contDiff.comp (contDiff_const.mul contDiff_id)

theorem slabWellCutoff_inner {S : ℝ} (hS : 0 < S) {z : ℝ} (hz : |z| ≤ S/2) :
    slabWellCutoff S z = 1 := by
  apply verticalCutoffBump.one_of_mem_closedBall
  change dist ((2/S)*z) 0 ≤ 1
  rw [dist_zero_right, Real.norm_eq_abs, abs_mul, abs_of_pos (div_pos (by norm_num) hS)]
  have hm := mul_le_mul_of_nonneg_left hz (div_pos (by norm_num : (0:ℝ)<2) hS).le
  have he : (2/S)*(S/2) = (1:ℝ) := by field_simp
  exact hm.trans_eq he

theorem slabWellCutoff_outer {S : ℝ} (hS : 0 < S) {z : ℝ} (hz : S ≤ |z|) :
    slabWellCutoff S z = 0 := by
  apply verticalCutoffBump.zero_of_le_dist
  change 2 ≤ dist ((2/S)*z) 0
  rw [dist_zero_right, Real.norm_eq_abs, abs_mul, abs_of_pos (div_pos (by norm_num) hS)]
  have hm := mul_le_mul_of_nonneg_left hz (div_pos (by norm_num : (0:ℝ)<2) hS).le
  have he : (2/S)*S = (2:ℝ) := by field_simp
  exact he.symm.le.trans hm

def countertermWellSum (freq scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (r : PlanarPosition) : ℝ :=
  ∑ i, (1 + localizedCounterterm freq u i / scale) * manufacturedPlanarWell (r-u i)

def manufacturedWellField (freq scale S : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (x : Position) : ℝ :=
  slabWellCutoff S (positionSplitCoordinates x).2 *
    countertermWellSum freq scale u (positionSplitCoordinates x).1

theorem countertermWellSum_C7 (freq scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) :
    ContDiff ℝ 7 (countertermWellSum freq scale u) := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul (manufacturedPlanarWell_C7.comp (contDiff_id.sub contDiff_const))

theorem manufacturedWellField_C7 (freq scale S : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) : ContDiff ℝ 7 (manufacturedWellField freq scale S u) :=
  ((slabWellCutoff_smooth S).of_le (by simp) |>.comp
    positionSplitCoordinates.contDiff.snd).mul
    ((countertermWellSum_C7 freq scale u).comp positionSplitCoordinates.contDiff.fst)

theorem countertermWellSum_nonpositive (freq : ℝ) {scale : ℝ} (hscale : 0 ≤ scale)
    {m : ℕ} (u : Fin m → PlanarPosition) (r : PlanarPosition) :
    countertermWellSum freq scale u r ≤ 0 := by
  apply Finset.sum_nonpos
  intro i _
  exact mul_nonpos_of_nonneg_of_nonpos
    (add_nonneg zero_le_one (div_nonneg (localizedCounterterm_nonnegative freq u i) hscale))
    (manufacturedPlanarWell_nonpositive _)

theorem manufacturedWellField_nonpositive (freq : ℝ) {scale : ℝ} (hscale : 0 ≤ scale)
    (S : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (x : Position) :
    manufacturedWellField freq scale S u x ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos (slabWellCutoff_bounds _ _).1
    (countertermWellSum_nonpositive freq hscale u _)

theorem manufacturedWellField_inner (freq scale : ℝ) {S : ℝ} (hS : 0 < S)
    {m : ℕ} (u : Fin m → PlanarPosition) (x : Position)
    (hx : |(positionSplitCoordinates x).2| ≤ S/2) :
    manufacturedWellField freq scale S u x =
      countertermWellSum freq scale u (positionSplitCoordinates x).1 := by
  simp only [manufacturedWellField, slabWellCutoff_inner hS hx, one_mul]

theorem manufacturedWellField_outer (freq scale : ℝ) {S : ℝ} (hS : 0 < S)
    {m : ℕ} (u : Fin m → PlanarPosition) (x : Position)
    (hx : S ≤ |(positionSplitCoordinates x).2|) :
    manufacturedWellField freq scale S u x = 0 := by
  simp only [manufacturedWellField, slabWellCutoff_outer hS hx, zero_mul]

theorem countertermWellSum_zero_far (freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (r : PlanarPosition)
    (hr : ∀ i, 1 ≤ ‖r-u i‖) : countertermWellSum freq scale u r = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [manufacturedPlanarWell_zero_of_norm_ge_one (hr i), mul_zero]

theorem manufacturedWellField_support (freq scale : ℝ) {S R : ℝ}
    (hS : 0 < S) (hR : 0 ≤ R) {m : ℕ} (u : Fin m → PlanarPosition)
    (hu : ∀ i, ‖u i‖ ≤ R) :
    tsupport (manufacturedWellField freq scale S u) ⊆
      Metric.closedBall (0 : Position) (R+S+1) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  have hz : |(positionSplitCoordinates x).2| < S := by
    by_contra hn
    exact hx (manufacturedWellField_outer freq scale hS u x (le_of_not_gt hn))
  have hr : ‖(positionSplitCoordinates x).1‖ < R+1 := by
    by_contra hn
    apply hx
    unfold manufacturedWellField
    rw [countertermWellSum_zero_far freq scale u _ (fun i => ?_), mul_zero]
    have ht : ‖(positionSplitCoordinates x).1‖ ≤
        ‖(positionSplitCoordinates x).1-u i‖ + ‖u i‖ := by
      simpa only [sub_add_cancel] using norm_add_le ((positionSplitCoordinates x).1-u i) (u i)
    linarith [hu i, le_of_not_gt hn]
  rw [Metric.mem_closedBall, dist_zero_right]
  have hs := positionSplitCoordinates_norm_sq x
  have hr2 := (sq_le_sq₀ (norm_nonneg _) (by linarith : 0 ≤ R+1)).mpr hr.le
  have hz2 := (sq_le_sq₀ (abs_nonneg _) hS.le).mpr hz.le
  rw [sq_abs] at hz2
  nlinarith [norm_nonneg x]

theorem manufacturedWellField_compact (freq scale : ℝ) {S : ℝ} (hS : 0 < S)
    {m : ℕ} (u : Fin m → PlanarPosition) :
    HasCompactSupport (manufacturedWellField freq scale S u) := by
  let R : ℝ := ∑ i, ‖u i‖
  have hR : 0 ≤ R := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hu (i : Fin m) : ‖u i‖ ≤ R :=
    Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  exact (isCompact_closedBall (0 : Position) (R+S+1)).of_isClosed_subset
    (isClosed_tsupport _) (manufacturedWellField_support freq scale hS hR u hu)

theorem positionSplitCoordinates_fst_zero (x : Position) :
    (positionSplitCoordinates x).1 0 = x 0 := rfl

theorem positionSplitCoordinates_fst_one (x : Position) :
    (positionSplitCoordinates x).1 1 = x 1 := rfl

theorem positionSplitCoordinates_snd (x : Position) :
    (positionSplitCoordinates x).2 = x 2 := rfl

theorem manufacturedWellField_support_slab (freq scale : ℝ) {S R H : ℝ}
    (hS : 0 < S) (hH : R+1 ≤ H) {m : ℕ} (u : Fin m → PlanarPosition)
    (hu : ∀ i, ‖u i‖ ≤ R) :
    tsupport (manufacturedWellField freq scale S u) ⊆ slabDomain H S := by
  apply closure_minimal _ (slabDomain_isClosed H S)
  intro x hx
  have hz : |(positionSplitCoordinates x).2| ≤ S := by
    by_contra hn
    exact hx (manufacturedWellField_outer freq scale hS u x (le_of_not_ge hn))
  have hnear : ∃ i, ‖(positionSplitCoordinates x).1-u i‖ < 1 := by
    by_contra hn
    apply hx
    unfold manufacturedWellField
    rw [countertermWellSum_zero_far freq scale u _ (fun i =>
      le_of_not_gt (fun hi => hn ⟨i, hi⟩)), mul_zero]
  obtain ⟨i, hi⟩ := hnear
  have hr : ‖(positionSplitCoordinates x).1‖ ≤ H := by
    have ht : ‖(positionSplitCoordinates x).1‖ ≤
        ‖(positionSplitCoordinates x).1-u i‖ + ‖u i‖ := by
      simpa only [sub_add_cancel] using norm_add_le ((positionSplitCoordinates x).1-u i) (u i)
    linarith [hu i]
  have h0 := (PiLp.norm_apply_le (positionSplitCoordinates x).1 0).trans hr
  have h1 := (PiLp.norm_apply_le (positionSplitCoordinates x).1 1).trans hr
  exact ⟨by simpa only [Real.norm_eq_abs, positionSplitCoordinates_fst_zero] using h0,
    by simpa only [Real.norm_eq_abs, positionSplitCoordinates_fst_one] using h1,
    by simpa only [positionSplitCoordinates_snd] using hz⟩

private theorem well_zero_away_from_near_site {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 2 ≤ ‖u i-u j‖) (r : PlanarPosition)
    (i : Fin m) (hi : ‖r-u i‖ < 1) (j : Fin m) (hji : j ≠ i) :
    manufacturedPlanarWell (r-u j) = 0 := by
  apply manufacturedPlanarWell_zero_of_norm_ge_one
  have ht : ‖u i-u j‖ ≤ ‖r-u i‖ + ‖r-u j‖ := by
    simpa only [dist_eq_norm, norm_sub_rev (u i) r] using dist_triangle (u i) r (u j)
  linarith [hsep i j hji.symm]

/-- Disjoint planar supports prevent the counterterm perturbation from
growing with the number of sites. -/
theorem countertermWellSum_lower (freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → 2 ≤ ‖u i-u j‖)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i / scale ∧
      localizedCounterterm freq u i / scale ≤ δ) (r : PlanarPosition) :
    planarWellSum u r - δ*PlanarSobolev.wellBound ≤ countertermWellSum freq scale u r := by
  classical
  by_cases hnear : ∃ i, ‖r-u i‖ < 1
  · obtain ⟨i, hi⟩ := hnear
    have hz := well_zero_away_from_near_site u hsep r i hi
    have hsum : planarWellSum u r = manufacturedPlanarWell (r-u i) := by
      unfold planarWellSum
      exact Finset.sum_eq_single i (fun j _ hji => hz j hji) (by simp)
    have hsum' : countertermWellSum freq scale u r =
        (1+localizedCounterterm freq u i/scale)*manufacturedPlanarWell (r-u i) := by
      unfold countertermWellSum
      exact Finset.sum_eq_single i (fun j _ hji => by rw [hz j hji, mul_zero]) (by simp)
    rw [hsum, hsum']
    have hw : -PlanarSobolev.wellBound ≤ manufacturedPlanarWell (r-u i) := by
      exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using
        PlanarSobolev.wellBound_spec (r-u i))).1
    have h1 := mul_le_mul_of_nonneg_left hw (hcoeff i).1
    have h2 := mul_le_mul_of_nonneg_right (hcoeff i).2 PlanarSobolev.wellBound_nonnegative
    nlinarith only [h1, h2]
  · have hz (i : Fin m) : manufacturedPlanarWell (r-u i) = 0 :=
      manufacturedPlanarWell_zero_of_norm_ge_one (le_of_not_gt (fun hi => hnear ⟨i, hi⟩))
    simp only [planarWellSum, countertermWellSum, hz, mul_zero, Finset.sum_const_zero]
    linarith [mul_nonneg hδ PlanarSobolev.wellBound_nonnegative]

/-- Global lower comparison to the separable uncapped multiwell field. -/
theorem manufacturedWellField_lower (freq : ℝ) {scale : ℝ} (hscale : 0 ≤ scale)
    (S : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 2 ≤ ‖u i-u j‖) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i / scale ∧
      localizedCounterterm freq u i / scale ≤ δ) (x : Position) :
    planarWellSum u (positionSplitCoordinates x).1 - δ*PlanarSobolev.wellBound ≤
      manufacturedWellField freq scale S u x := by
  apply (countertermWellSum_lower freq scale u hsep hδ hcoeff _).trans
  exact le_mul_of_le_one_left (countertermWellSum_nonpositive freq hscale u _)
    (slabWellCutoff_bounds S _).2

end ContinuumCoulomb

end

end OAI
