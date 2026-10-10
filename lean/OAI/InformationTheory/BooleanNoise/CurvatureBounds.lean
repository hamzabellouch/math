import OAI.InformationTheory.BooleanNoise.CurvatureCertificates
import OAI.InformationTheory.BooleanNoise.InverseScalars
import OAI.InformationTheory.BooleanNoise.SmallCurvatureAux
import OAI.InformationTheory.BooleanNoise.MediumCurvature
import OAI.InformationTheory.BooleanNoise.LargeCurvature
import OAI.InformationTheory.BooleanNoise.InverseRegularity

namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

def curvatureModel (u t : ℝ) : ℝ :=
  ((1 + u ^ 2) * t - u) / ((1 - u ^ 2) ^ 2 * t ^ 3)

private def smallCoarseBound (z : ℝ) : ℝ :=
  ((4 / 3) + (2 / 3) * (z / (1 - z))) / ((1 - z) ^ 2 * (1 + z / 3) ^ 3)

private theorem smallCoarseBound_lt_ten_sevenths {z : ℝ}
    (hz0 : 0 ≤ z) (hz25 : z ≤ 1 / 25) : smallCoarseBound z < 10 / 7 := by
  have hz1 : 0 < 1 - z := by linarith
  have hratio : z / (1 - z) ≤ 1 / 24 := (div_le_iff₀ hz1).mpr (by linarith)
  have hnum : (4 / 3 : ℝ) + (2 / 3) * (z / (1 - z)) ≤ 49 / 36 := by linarith
  have hzsq : z ^ 2 ≤ 1 / 625 := by
    nlinarith [mul_nonneg hz0 (show 0 ≤ 1 / 25 - z by linarith)]
  have hcube : 1 + z ≤ (1 + z / 3) ^ 3 := by
    nlinarith [sq_nonneg z, pow_nonneg hz0 3]
  have hbase : (599 / 625 : ℝ) ≤ (1 - z) ^ 2 * (1 + z) := by
    nlinarith [pow_nonneg hz0 3]
  have hden : (599 / 625 : ℝ) ≤ (1 - z) ^ 2 * (1 + z / 3) ^ 3 :=
    hbase.trans (mul_le_mul_of_nonneg_left hcube (sq_nonneg _))
  have hden0 : 0 < (1 - z) ^ 2 * (1 + z / 3) ^ 3 := by linarith
  apply (div_lt_iff₀ hden0).mpr
  calc
    (4 / 3 : ℝ) + (2 / 3) * (z / (1 - z)) ≤ 49 / 36 := hnum
    _ < (10 / 7) * (599 / 625) := by norm_num
    _ ≤ (10 / 7) * ((1 - z) ^ 2 * (1 + z / 3) ^ 3) :=
      mul_le_mul_of_nonneg_left hden (by norm_num)

private theorem normalized_small_curvature_le {z a : ℝ}
    (hz0 : 0 < z) (hz25 : z ≤ 1 / 25)
    (hal : 1 + z / 3 ≤ a) (hau : a ≤ 1 + z / (3 * (1 - z))) :
    (((1 + z) * a - 1) / z) / ((1 - z) ^ 2 * a ^ 3) ≤ smallCoarseBound z := by
  have hz1 : 0 < 1 - z := by linarith
  have ha0 : 0 < a := by linarith
  have hnum : ((1 + z) * a - 1) / z ≤ (4 / 3) + (2 / 3) * (z / (1 - z)) := by
    calc
      ((1 + z) * a - 1) / z ≤
          ((1 + z) * (1 + z / (3 * (1 - z))) - 1) / z :=
        div_le_div_of_nonneg_right
          (sub_le_sub_right (mul_le_mul_of_nonneg_left hau (by linarith)) 1) hz0.le
      _ = (4 / 3) + (2 / 3) * (z / (1 - z)) := by
        field_simp [hz0.ne', hz1.ne']
        ring
  have hupper0 : 0 ≤ (4 / 3 : ℝ) + (2 / 3) * (z / (1 - z)) := by positivity
  have hden0 : 0 < (1 - z) ^ 2 * (1 + z / 3) ^ 3 := by positivity
  have hdena0 : 0 < (1 - z) ^ 2 * a ^ 3 := by positivity
  have hdencmp : (1 - z) ^ 2 * (1 + z / 3) ^ 3 ≤ (1 - z) ^ 2 * a ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hal 3) (sq_nonneg _)
  calc
    (((1 + z) * a - 1) / z) / ((1 - z) ^ 2 * a ^ 3) ≤
        ((4 / 3) + (2 / 3) * (z / (1 - z))) / ((1 - z) ^ 2 * a ^ 3) :=
      div_le_div_of_nonneg_right hnum hdena0.le
    _ ≤ smallCoarseBound z := div_le_div_of_nonneg_left hupper0 hden0 hdencmp

theorem curvatureModel_small_of_cubic_bounds {u t : ℝ}
    (hu0 : 0 < u) (hu5 : u ≤ 1 / 5)
    (hl : u + u ^ 3 / 3 ≤ t) (hu : t ≤ u + u ^ 3 / (3 * (1 - u ^ 2))) :
    curvatureModel u t < 1 / ell := by
  have hz0 : 0 < u ^ 2 := sq_pos_of_pos hu0
  have hz25 : u ^ 2 ≤ 1 / 25 := by
    nlinarith [mul_nonneg hu0.le (show 0 ≤ 1 / 5 - u by linarith)]
  have hq : 0 < 1 - u ^ 2 := by linarith
  have ht0 : 0 < t := by nlinarith [pow_pos hu0 3]
  have hal : 1 + u ^ 2 / 3 ≤ t / u := by
    apply (le_div_iff₀ hu0).mpr
    nlinarith
  have hau : t / u ≤ 1 + u ^ 2 / (3 * (1 - u ^ 2)) := by
    apply (div_le_iff₀ hu0).mpr
    calc
      t ≤ u + u ^ 3 / (3 * (1 - u ^ 2)) := hu
      _ = (1 + u ^ 2 / (3 * (1 - u ^ 2))) * u := by ring
  have he : curvatureModel u t =
      (((1 + u ^ 2) * (t / u) - 1) / u ^ 2) / ((1 - u ^ 2) ^ 2 * (t / u) ^ 3) := by
    unfold curvatureModel
    field_simp [hu0.ne', ht0.ne', hq.ne']
  rw [he]
  exact (normalized_small_curvature_le hz0 hz25 hal hau).trans_lt
    ((smallCoarseBound_lt_ten_sevenths hz0.le hz25).trans ten_sevenths_lt_inv_ell)

theorem curvatureModel_artanh_small {u : ℝ} (hu0 : 0 < u) (hu5 : u ≤ 1 / 5) :
    curvatureModel u (Real.artanh u) < 1 / ell := by
  have hu : u ∈ Set.Ico (0 : ℝ) 1 := ⟨hu0.le, by linarith⟩
  exact curvatureModel_small_of_cubic_bounds hu0 hu5
    (cubic_le_artanh hu) (artanh_le_cubic_tail hu)

theorem rSecondDeriv_le_inv_ell {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ s0) :
    rSecondDeriv s ≤ 1 / ell := by
  by_cases hs_zero : s = 0
  · subst s
    rw [rSecondDeriv_zero]
    exact (show (4 / 3 : ℝ) < 10 / 7 by norm_num).trans ten_sevenths_lt_inv_ell |>.le
  · have hsp : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs_zero)
    have hsell : s < ell := hs.trans_lt s0_lt_ell
    have hu := psiInv_mem_Ioo ⟨hsp, hsell⟩
    have hu5 : psiInv s ≤ 1 / 5 := by
      apply (strictMonoOn_psi.le_iff_le ⟨hu.1.le, hu.2.le⟩ (by norm_num)).mp
      rw [psi_psiInv hs0 hsell]
      exact hs
    change (if s ≤ 0 then 4 / 3 else curvatureModel (psiInv s) (Real.artanh (psiInv s))) ≤ _
    rw [ite_eq_right (not_le.mpr hsp)]
    exact (curvatureModel_artanh_small hu.1 hu5).le

theorem entropy_curvature_bound {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    entropy u ^ 2 * curvatureModel u (Real.artanh u) ≤ 2 / 3 := by
  by_cases hz : u ^ 2 ≤ 2 / 3
  · exact medium_curvature_bound hu0 hu1 hz
  · exact large_curvature_bound hu0.le hu1 (le_of_not_ge hz)

theorem inverseEntropy_curvature_bound {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) ell) :
    (ell - s) ^ 2 * rSecondDeriv s ≤ 2 / 3 := by
  have hu := psiInv_mem_Ioo hs
  have h := entropy_curvature_bound hu.1 hu.2
  rw [rSecondDeriv, ite_eq_right (not_le.mpr hs.1)]
  simpa only [entropy, psi_psiInv hs.1.le hs.2, curvatureModel] using h

theorem L_curvature_bound {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) ell) :
    x ^ 2 * rSecondDeriv (ell - x) ≤ 2 / 3 := by
  have hs : ell - x ∈ Ioo (0 : ℝ) ell := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  simpa only [sub_sub_cancel] using inverseEntropy_curvature_bound hs

theorem LDeriv_curvature_bound {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) ell) :
    x ^ 2 * deriv LDeriv x ≤ 2 / 3 := by
  rw [(hasDerivAt_LDeriv_of_lt hx).deriv]
  exact L_curvature_bound hx

theorem hasDerivAt_deriv_L_of_lt {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) ell) :
    HasDerivAt (deriv L) (rSecondDeriv (ell - x)) x := by
  have he : deriv L =ᶠ[𝓝 x] LDeriv := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact (hasDerivAt_L_of_lt hy).deriv
  exact (hasDerivAt_LDeriv_of_lt hx).congr_of_eventuallyEq he

theorem L_second_deriv_bound {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) ell) :
    x ^ 2 * deriv (deriv L) x ≤ 2 / 3 := by
  rw [(hasDerivAt_deriv_L_of_lt hx).deriv]
  exact L_curvature_bound hx

theorem hasDerivAt_deriv_r_of_pos {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) ell) :
    HasDerivAt (deriv r) (rSecondDeriv s) s := by
  have he : deriv r =ᶠ[𝓝 s] rDeriv := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with y hy
    exact (hasDerivAt_r hy).deriv
  exact (hasDerivAt_rDeriv hs).congr_of_eventuallyEq he

theorem r_second_deriv_bound {s : ℝ} (hs0 : 0 < s) (hs : s ≤ s0) :
    deriv (deriv r) s ≤ 1 / ell := by
  rw [(hasDerivAt_deriv_r_of_pos ⟨hs0, hs.trans_lt s0_lt_ell⟩).deriv]
  exact rSecondDeriv_le_inv_ell hs0.le hs

end LeanBlast.CourtadeKumar

end

end OAI
