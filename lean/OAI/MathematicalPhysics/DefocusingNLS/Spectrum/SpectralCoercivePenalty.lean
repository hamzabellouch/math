import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoerciveInverse

namespace OAI

/-! Uniform inverse and pressure estimates with a varying coercive base form. -/

open InnerProductSpace
namespace DefocusingNLS

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

noncomputable def spectralCoercivePenaltyForm (B : E →L[ℝ] E →L[ℝ] ℝ)
    (V : E →L[ℝ] H) (P : H →L[ℝ] H) (a : ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  let I : H →L[ℝ] H →L[ℝ] ℝ := innerSL ℝ
  B+a⁻¹ • I.bilinearComp (P.comp V) V

theorem spectralCoercivePenaltyForm_apply (B : E →L[ℝ] E →L[ℝ] ℝ)
    (V : E →L[ℝ] H) (P : H →L[ℝ] H) (a : ℝ) (u v : E) :
    spectralCoercivePenaltyForm B V P a u v=B u v+a⁻¹*inner ℝ (P (V u)) (V v) := rfl

theorem spectralCoercivePenaltyForm_lower (B : E →L[ℝ] E →L[ℝ] ℝ)
    (c : ℝ) (hB : ∀ u, c*‖u‖^2 ≤ B u u)
    (V : E →L[ℝ] H) (P : H →L[ℝ] H) (hP : ∀ x, 0 ≤ inner ℝ (P x) x)
    (a : ℝ) (ha : 0 < a) (u : E) :
    c*‖u‖^2 ≤ spectralCoercivePenaltyForm B V P a u u := by
  rw [spectralCoercivePenaltyForm_apply]
  exact (hB u).trans (le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr ha.le) (hP _)))

theorem spectralCoercivePenaltyForm_coercive (B : E →L[ℝ] E →L[ℝ] ℝ)
    (c : ℝ) (hc : 0 < c) (hB : ∀ u, c*‖u‖^2 ≤ B u u)
    (V : E →L[ℝ] H) (P : H →L[ℝ] H) (hP : ∀ x, 0 ≤ inner ℝ (P x) x)
    (a : ℝ) (ha : 0 < a) : IsCoercive (spectralCoercivePenaltyForm B V P a) := by
  refine ⟨c,hc,fun u => ?_⟩
  simpa only [pow_two,mul_assoc] using spectralCoercivePenaltyForm_lower B c hB V P hP a ha u

variable [CompleteSpace E]

noncomputable def spectralCoercivePenaltyInverse (B : E →L[ℝ] E →L[ℝ] ℝ)
    (c : ℝ) (hc : 0 < c) (hB : ∀ u, c*‖u‖^2 ≤ B u u)
    (V : E →L[ℝ] H) (P : H →L[ℝ] H) (hP : ∀ x, 0 ≤ inner ℝ (P x) x)
    (a : ℝ) (ha : 0 < a) : StrongDual ℝ E →L[ℝ] E :=
  spectralCoerciveInverse _ (spectralCoercivePenaltyForm_coercive B c hc hB V P hP a ha)

theorem spectralCoercivePenaltyInverse_norm (B : E →L[ℝ] E →L[ℝ] ℝ)
    (c : ℝ) (hc : 0 < c) (hB : ∀ u, c*‖u‖^2 ≤ B u u)
    (V : E →L[ℝ] H) (P : H →L[ℝ] H) (hP : ∀ x, 0 ≤ inner ℝ (P x) x)
    (a : ℝ) (ha : 0 < a) (F : StrongDual ℝ E) :
    ‖spectralCoercivePenaltyInverse B c hc hB V P hP a ha F‖ ≤ ‖F‖/c :=
  spectralCoerciveInverse_norm _ _ c hc
    (spectralCoercivePenaltyForm_lower B c hB V P hP a ha) F

theorem spectralCoercivePenaltyInverse_energy (B : E →L[ℝ] E →L[ℝ] ℝ)
    (c : ℝ) (hc : 0 < c) (hB : ∀ u, c*‖u‖^2 ≤ B u u)
    (V : E →L[ℝ] H) (P : H →L[ℝ] H) (hP : ∀ x, 0 ≤ inner ℝ (P x) x)
    (a : ℝ) (ha : 0 < a) (F : StrongDual ℝ E) :
    inner ℝ (P (V (spectralCoercivePenaltyInverse B c hc hB V P hP a ha F)))
      (V (spectralCoercivePenaltyInverse B c hc hB V P hP a ha F)) ≤ a*‖F‖^2/c := by
  let u := spectralCoercivePenaltyInverse B c hc hB V P hP a ha F
  have he := spectralCoerciveInverse_equation (spectralCoercivePenaltyForm B V P a)
    (spectralCoercivePenaltyForm_coercive B c hc hB V P hP a ha) F u
  change spectralCoercivePenaltyForm B V P a u u=F u at he
  rw [spectralCoercivePenaltyForm_apply] at he
  have hbu : 0 ≤ B u u := (mul_nonneg hc.le (sq_nonneg ‖u‖)).trans (hB u)
  have hn := spectralCoercivePenaltyInverse_norm B c hc hB V P hP a ha F
  have hf : F u ≤ ‖F‖*‖u‖ := (le_abs_self _).trans (F.le_opNorm u)
  calc
    inner ℝ (P (V u)) (V u) = a*(a⁻¹*inner ℝ (P (V u)) (V u)) := by
      rw [← mul_assoc,mul_inv_cancel₀ ha.ne',one_mul]
    _ ≤ a*(F u) := mul_le_mul_of_nonneg_left (by linarith) ha.le
    _ ≤ a*(‖F‖*‖u‖) := mul_le_mul_of_nonneg_left hf ha.le
    _ ≤ a*(‖F‖*(‖F‖/c)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hn (norm_nonneg F)) ha.le
    _ = a*‖F‖^2/c := by ring

end DefocusingNLS

end OAI
