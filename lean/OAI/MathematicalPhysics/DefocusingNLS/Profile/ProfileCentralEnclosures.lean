import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileCertificateComparisons
import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileMatrixProduct

namespace OAI

/-! Modulus consequences of the exact central rational comparisons. -/

open Matrix
namespace DefocusingNLS.ProfileCertificate
open RationalComplex

theorem norm_toComplex_lt_of_sq (z : RationalComplex) (c : ℚ) (hc : 0 ≤ c)
    (h : normSq z < c^2) : ‖toComplex z‖ < (c : ℝ) := by
  have hh := (Rat.cast_lt (K := ℝ)).mpr h
  rw [← normSq_toComplex z, Complex.normSq_eq_norm_sq] at hh
  push_cast at hh
  have hc' : (0 : ℝ) ≤ c := Rat.cast_nonneg.mpr hc
  nlinarith [norm_nonneg (toComplex z)]

theorem norm_toComplex_lt_mul (z w : RationalComplex) (c : ℚ) (hc : 0 ≤ c)
    (h : normSq z < c^2*normSq w) : ‖toComplex z‖ < (c : ℝ)*‖toComplex w‖ := by
  have hh := (Rat.cast_lt (K := ℝ)).mpr h
  push_cast at hh
  rw [← normSq_toComplex z, ← normSq_toComplex w,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hh
  have hc' : (0 : ℝ) ≤ c := Rat.cast_nonneg.mpr hc
  have hn : 0 ≤ (c : ℝ)*‖toComplex w‖ := mul_nonneg hc' (norm_nonneg _)
  nlinarith [norm_nonneg (toComplex z)]

noncomputable def centralM : ℂ := toComplex result.value.b

theorem centralM_bounds : 9 < ‖centralM‖ ∧ ‖centralM‖ < 10 := by
  rcases central_bounds with ⟨hlo, hhi, _⟩
  have hl := (Rat.cast_lt (K := ℝ)).mpr hlo
  have hu := (Rat.cast_lt (K := ℝ)).mpr hhi
  rw [← normSq_toComplex, Complex.normSq_eq_norm_sq] at hl hu
  norm_num only [Rat.cast_ofNat] at hl hu
  constructor <;> dsimp [centralM] <;> nlinarith [norm_nonneg (toComplex result.value.b)]

theorem centralM_ne_zero : centralM ≠ 0 := by
  exact norm_pos_iff.mp (lt_trans (by norm_num) centralM_bounds.1)

/-- Every computed derivative entry has the required size relative to m0. -/
theorem central_derivative_entries :
    (∀ v ∈ [result.derivB.a, result.derivB.b, result.derivB.c, result.derivB.d,
      result.derivZ.a, result.derivZ.b, result.derivZ.c, result.derivZ.d],
      ‖toComplex v‖ < 20*‖centralM‖) := by
  have h := central_bounds
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hder, _⟩
  intro v hv
  exact norm_toComplex_lt_mul v result.value.b 20 (by norm_num) (by
    simpa only [show (20 : ℚ)^2 = 400 by norm_num] using hder v hv)

/-- Every entry of E is below the prescribed 50000 |m0| bound. -/
theorem central_error_entries :
    ∀ e ∈ [result.error.a, result.error.b, result.error.c, result.error.d],
      0 ≤ (e : ℝ) ∧ (e : ℝ) < 50000*‖centralM‖ := by
  have h := central_bounds
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, herr⟩
  intro e he
  obtain ⟨hpos, hsq⟩ := herr e he
  have hepos : 0 ≤ (e : ℝ) := Rat.cast_nonneg.mpr hpos
  have hs := (Rat.cast_lt (K := ℝ)).mpr hsq
  push_cast at hs
  rw [← normSq_toComplex, Complex.normSq_eq_norm_sq] at hs
  refine ⟨hepos, ?_⟩
  dsimp [centralM]
  nlinarith [norm_nonneg (toComplex result.value.b)]

end DefocusingNLS.ProfileCertificate

end OAI
