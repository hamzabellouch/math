import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeVertexMoment

namespace OAI

/-! Bounded Hilbert-valued tests recover the Lp norm on each finite
exhaustion set used in the source interpolation. The canonical test is
constructed explicitly and introduces no dimension-dependent constant. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

def sourceCanonicalDual (F : X → EuclideanSpace ℂ κ) (p : ℝ) (x : X) :
    EuclideanSpace ℂ κ := ((‖F x‖^(p-2):ℝ):ℂ) • F x

omit [MeasurableSpace X] in
theorem sourceCanonicalDual_norm (F : X → EuclideanSpace ℂ κ) {p : ℝ}
    (hp : 1 < p) (x : X) : ‖sourceCanonicalDual F p x‖ = ‖F x‖^(p-1) := by
  rw [sourceCanonicalDual,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  by_cases hzero : F x = 0
  · simp [hzero,Real.zero_rpow (show p-1 ≠ 0 by linarith)]
  · calc
      _ = ‖F x‖^(p-2)*‖F x‖^(1:ℝ) := by rw [Real.rpow_one]
      _ = ‖F x‖^(p-1) := by rw [← Real.rpow_add (norm_pos_iff.mpr hzero)]; congr 1; ring

omit [MeasurableSpace X] in
theorem sourceCanonicalDual_pairing (F : X → EuclideanSpace ℂ κ) {p : ℝ}
    (hp : 1 < p) (x : X) :
    ⟪sourceCanonicalDual F p x,F x⟫_ℂ = (‖F x‖^p:ℝ) := by
  have heq : ‖F x‖^(p-2)*‖F x‖^2 = ‖F x‖^p := by
    by_cases hzero : F x = 0
    · simp [hzero,Real.zero_rpow (show p ≠ 0 by linarith)]
    · rw [← Real.rpow_natCast,← Real.rpow_add (norm_pos_iff.mpr hzero)]
      congr 1
      push_cast
      ring
  rw [sourceCanonicalDual,inner_smul_left,Complex.conj_ofReal]
  have hre : (⟪F x,F x⟫_ℂ).re = ‖F x‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) (F x)
  have him : (⟪F x,F x⟫_ℂ).im = 0 := inner_self_im (𝕜 := ℂ) (F x)
  apply Complex.ext
  · simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,hre,zero_mul,sub_zero] using heq
  · simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,him,mul_zero,zero_mul,add_zero]

theorem source_bounded_lp_of_dual_tests (μ : Measure X) [IsFiniteMeasure μ]
    (F : X → EuclideanSpace ℂ κ) (hF : Measurable F) (A C p : ℝ)
    (hC : 0 ≤ C) (hp : 1 < p) (hbound : ∀ x, ‖F x‖ ≤ A)
    (htest : ∀ b : X → EuclideanSpace ℂ κ, Measurable b →
      (∃ B : ℝ, ∀ x, ‖b x‖ ≤ B) →
      ‖∫ x, ⟪b x,F x⟫_ℂ ∂μ‖ ≤ C*(∫ x, ‖b x‖^(p/(p-1)) ∂μ)^(1/(p/(p-1)))) :
    (∫ x, ‖F x‖^p ∂μ)^(1/p) ≤ C := by
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p-1 := by linarith
  have hDmeas : Measurable (sourceCanonicalDual F p) :=
    ((hF.norm.pow_const _).complex_ofReal).smul hF
  have hDbound : ∀ x, ‖sourceCanonicalDual F p x‖ ≤ A^(p-1) := by
    intro x
    rw [sourceCanonicalDual_norm F hp]
    exact Real.rpow_le_rpow (norm_nonneg _) (hbound x) hpm.le
  have h := htest (sourceCanonicalDual F p) hDmeas ⟨A^(p-1),hDbound⟩
  have hpair : (∫ x, ⟪sourceCanonicalDual F p x,F x⟫_ℂ ∂μ) =
      ((∫ x, ‖F x‖^p ∂μ):ℝ) := by
    simp_rw [sourceCanonicalDual_pairing F hp]
    exact integral_complex_ofReal
  have hpow (x : X) : ‖sourceCanonicalDual F p x‖^(p/(p-1)) = ‖F x‖^p := by
    rw [sourceCanonicalDual_norm F hp,← Real.rpow_mul (norm_nonneg _)]
    congr 1
    field_simp
  have hI0 : 0 ≤ ∫ x, ‖F x‖^p ∂μ :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  rw [hpair,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hI0] at h
  simp_rw [hpow] at h
  by_cases hz : (∫ x, ‖F x‖^p ∂μ) = 0
  · simpa only [hz,Real.zero_rpow (one_div_ne_zero hp0.ne')] using hC
  · have hi : 0 < ∫ x, ‖F x‖^p ∂μ := lt_of_le_of_ne hI0 (Ne.symm hz)
    have hdiv := (div_le_iff₀ (Real.rpow_pos_of_pos hi (1/(p/(p-1))))).mpr h
    have heq : (∫ x, ‖F x‖^p ∂μ)/(∫ x, ‖F x‖^p ∂μ)^(1/(p/(p-1))) =
        (∫ x, ‖F x‖^p ∂μ)^(1/p) := by
      calc
        _ = (∫ x, ‖F x‖^p ∂μ)^(1:ℝ)/(∫ x, ‖F x‖^p ∂μ)^(1/(p/(p-1))) := by rw [Real.rpow_one]
        _ = (∫ x, ‖F x‖^p ∂μ)^(1-1/(p/(p-1))) := (Real.rpow_sub hi _ _).symm
        _ = _ := by congr 1; field_simp; ring
    exact heq ▸ hdiv

end LipschitzHilbert

end

end OAI
