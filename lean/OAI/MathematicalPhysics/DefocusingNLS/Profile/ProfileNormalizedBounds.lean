import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileEntryBounds
import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileLinearMap

namespace OAI

/-! Normalized numerical bounds before division by the free-profile matching denominator. -/

open Matrix
namespace DefocusingNLS.ProfileCertificate
open RationalComplex

attribute [local irreducible] profileProduct

private theorem lt_norm_of_sq (v : RationalComplex) (c : ℚ) (hc : 0 ≤ c)
    (h : c^2 < normSq v) : (c : ℝ) < ‖toComplex v‖ := by
  have hh := (Rat.cast_lt (K := ℝ)).mpr h
  rw [← normSq_toComplex v, Complex.normSq_eq_norm_sq] at hh
  push_cast at hh
  have hc' : (0 : ℝ) ≤ c := Rat.cast_nonneg.mpr hc
  nlinarith [norm_nonneg (toComplex v)]

private theorem central_u : centralNormalized 0 0 =
    toComplex (quotient result.value.a result.value.b) := by
  exact (toComplex_quotient _ _).symm

theorem central_u_bound : ‖centralNormalized 0 0‖ < (318/100 : ℝ) := by
  rcases linear_bounds with ⟨_, _, _, hu, _⟩
  rw [central_u]
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    norm_toComplex_lt_of_sq _ (318/100) (by norm_num) hu

theorem central_denominator_bound : (234/100 : ℝ) <
    ‖1-(Complex.I*(centerZ : ℝ)/5)*centralNormalized 0 0‖ := by
  rcases linear_bounds with ⟨_, _, hd, _⟩
  have h := lt_norm_of_sq _ (234/100) (by norm_num) hd
  have hi : toComplex (⟨0,centerZ/5⟩ : RationalComplex) = Complex.I*(centerZ : ℝ)/5 := by
    apply Complex.ext <;> simp [toComplex]
  simpa only [map_sub, map_one, map_mul, hi, ← central_u, Rat.cast_div, Rat.cast_ofNat] using h

theorem central_last_entry_bound : ‖centralNormalized 1 1‖ < (1/1000000000000 : ℝ) := by
  rcases central_bounds with ⟨_, _, _, _, _, _, hd, _⟩
  have h := norm_toComplex_lt_mul result.value.d result.value.b (1/1000000000000)
    (by norm_num) hd
  change ‖toComplex result.value.d/centralM‖ < _
  rw [norm_div]
  exact (div_lt_iff₀ (norm_pos_iff.mpr centralM_ne_zero)).mpr (by
    simpa only [centralM, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h)

theorem centralX_bound : ‖centralX‖ < (159/1000 : ℝ) := by
  rcases linear_bounds with ⟨_, _, _, _, hx, _⟩
  simpa only [centralX, Rat.cast_div, Rat.cast_ofNat] using
    norm_toComplex_lt_of_sq _ (159/1000) (by norm_num) hx

theorem centralY_bound : ‖centralY‖ < (124/1000 : ℝ) := by
  rcases linear_bounds with ⟨_, _, _, _, _, hy, _⟩
  simpa only [centralY, Rat.cast_div, Rat.cast_ofNat] using
    norm_toComplex_lt_of_sq _ (124/1000) (by norm_num) hy

theorem free_linear_size (b z : ℝ) (hb : |b| ≤ (radius : ℝ)) (hz : |z| ≤ (radius : ℝ)) :
    ‖(b : ℂ)*centralX+(z : ℂ)*centralY‖ ≤ (283/1000 : ℝ)*(radius : ℝ) := by
  have hδ : 0 ≤ (radius : ℝ) := by norm_num [radius]
  calc
    _ ≤ ‖(b : ℂ)*centralX‖+‖(z : ℂ)*centralY‖ := norm_add_le _ _
    _ = |b| *‖centralX‖+|z| *‖centralY‖ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (radius : ℝ)*(159/1000)+(radius : ℝ)*(124/1000) :=
      add_le_add (mul_le_mul hb centralX_bound.le (norm_nonneg _) hδ)
        (mul_le_mul hz centralY_bound.le (norm_nonneg _) hδ)
    _ = _ := by ring

theorem normalizedProfile_last_remainder (b z : ℝ)
    (hb : |b| ≤ (radius : ℝ)) (hz : |z| ≤ (radius : ℝ)) :
    ‖normalizedProfile b z 1 1-((b : ℂ)*centralX+(z : ℂ)*centralY)‖ <
      (1/1000000000000 : ℝ)+50000*(radius : ℝ)^2 := by
  have hx : toComplex result.derivB.d/centralM = centralX := (toComplex_quotient _ _).symm
  have hy : toComplex result.derivZ.d/centralM = centralY := (toComplex_quotient _ _).symm
  have he : normalizedProfile b z 1 1-centralNormalized 1 1-
      ((b : ℂ)*centralX+(z : ℂ)*centralY) =
      (profileProduct ((centerB : ℝ)+b) ((centerZ : ℝ)+z) 34 1 1-
        toComplex result.value.d-(b : ℂ)*toComplex result.derivB.d-
        (z : ℂ)*toComplex result.derivZ.d)/centralM := by
    rw [← hx, ← hy]
    change profileProduct ((centerB : ℝ)+b) ((centerZ : ℝ)+z) 34 1 1/centralM-
      toComplex result.value.d/centralM-
      ((b : ℂ)*(toComplex result.derivB.d/centralM)+(z : ℂ)*(toComplex result.derivZ.d/centralM)) = _
    ring
  have hr : ‖normalizedProfile b z 1 1-centralNormalized 1 1-
      ((b : ℂ)*centralX+(z : ℂ)*centralY)‖ < 50000*(radius : ℝ)^2 := by
    rw [he, norm_div]
    apply (div_lt_iff₀ (norm_pos_iff.mpr centralM_ne_zero)).mpr
    convert! profile_entry_remainder b z hb hz 1 1 using 1
    ring
  calc
    _ = ‖(normalizedProfile b z 1 1-centralNormalized 1 1-
        ((b : ℂ)*centralX+(z : ℂ)*centralY))+centralNormalized 1 1‖ := by congr 1; ring
    _ ≤ ‖normalizedProfile b z 1 1-centralNormalized 1 1-
        ((b : ℂ)*centralX+(z : ℂ)*centralY)‖+‖centralNormalized 1 1‖ := norm_add_le _ _
    _ < _ := by linarith [central_last_entry_bound]

end DefocusingNLS.ProfileCertificate

end OAI
