import OAI.Analysis.KadisonKastler.ModularRadonScaling
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric

namespace OAI

/-! # The modular pairing equation for arbitrary self-adjoint commutant elements -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem modular_radon_nikodym_nonnegative (Ω : H) (b : H →L[ℂ] H)
    (hb : b ∈ M.commutant) (hb0 : 0 ≤ b) (z : ℂ) (hz : 0 < z.re) :
    ∃ x : Algebra M, IsSelfAdjoint x ∧ ‖x‖ ≤ (1 + ‖b‖) / z.re ∧
      ∀ a : selfAdjoint (Algebra M),
        (inner ℂ (a.val.val Ω) (b Ω)).re =
          (z * inner ℂ (a.val.val Ω) (x.val Ω)).re := by
  let R : ℝ := 1 + ‖b‖
  have hR : 0 < R := by dsimp [R]; positivity
  let c : H →L[ℂ] H := R⁻¹ • b
  have hc : c ∈ M.commutant :=
    (M.commutant.toStarSubalgebra.restrictScalars ℝ).smul_mem hb R⁻¹
  have hc0 : 0 ≤ c := smul_nonneg (inv_nonneg.mpr hR.le) hb0
  have hcn : ‖c‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    calc
      R⁻¹ * ‖b‖ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left (by dsimp [R]; linarith)
        (inv_nonneg.mpr hR.le)
      _ = 1 := inv_mul_cancel₀ hR.ne'
  have hc1 : c ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg c hc0).mp hcn
  obtain ⟨x, hx, hxn, hxp⟩ := modular_radon_nikodym_positive_halfPlane Ω c hc hc0 hc1 z hz
  have he : b = R • c := by
    dsimp [c]
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  refine ⟨R • x, ?_, ?_, ?_⟩
  · change star (R • x) = R • x
    rw [star_smul, star_trivial, hx.star_eq]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    exact (mul_le_mul_of_nonneg_left hxn hR.le).trans_eq (by dsimp [R]; ring)
  · intro a
    have hi (v : H) : inner ℂ (a.val.val Ω) (R • v) = (R : ℂ) * inner ℂ (a.val.val Ω) v := by
      rw [← Complex.coe_smul R, inner_smul_right]
    rw [he]
    change (inner ℂ (a.val.val Ω) (R • c Ω)).re =
      (z * inner ℂ (a.val.val Ω) (R • x.val Ω)).re
    rw [hi, hi]
    have hr (w : ℂ) : ((R : ℂ) * w).re = R * w.re := by simp
    calc
      ((R : ℂ) * inner ℂ (a.val.val Ω) (c Ω)).re =
          R * (inner ℂ (a.val.val Ω) (c Ω)).re := hr _
      _ = R * (z * inner ℂ (a.val.val Ω) (x.val Ω)).re := by rw [hxp a]
      _ = ((R : ℂ) * (z * inner ℂ (a.val.val Ω) (x.val Ω))).re := (hr _).symm
      _ = (z * ((R : ℂ) * inner ℂ (a.val.val Ω) (x.val Ω))).re := by congr 1; ring

/-- The exact real pairing conclusion needed for bounded Tomita resolvents. -/
theorem modular_radon_nikodym_selfAdjoint (Ω : H) (b : Algebra M.commutant)
    (hb : IsSelfAdjoint b) (z : ℂ) (hz : 0 < z.re) :
    ∃ x : Algebra M, IsSelfAdjoint x ∧ ‖x‖ ≤ 2 * (1 + ‖b‖) / z.re ∧
      ∀ a : selfAdjoint (Algebra M),
        (inner ℂ (a.val.val Ω) (b.val Ω)).re =
          (z * inner ℂ (a.val.val Ω) (x.val Ω)).re := by
  let : PartialOrder (Algebra M.commutant) := CStarAlgebra.spectralOrder _
  let : Preorder (Algebra M.commutant) := (CStarAlgebra.spectralOrder _).toPreorder
  let : LE (Algebra M.commutant) := (CStarAlgebra.spectralOrder _).toLE
  let : StarOrderedRing (Algebra M.commutant) := CStarAlgebra.spectralOrderedRing _
  have hp : 0 ≤ (b⁺).val := by
    have h := map_rel M.commutant.toStarSubalgebra.subtype (CFC.posPart_nonneg b)
    change M.commutant.toStarSubalgebra.subtype 0 ≤ (b⁺).val at h
    simpa only [map_zero] using h
  have hn : 0 ≤ (b⁻).val := by
    have h := map_rel M.commutant.toStarSubalgebra.subtype (CFC.negPart_nonneg b)
    change M.commutant.toStarSubalgebra.subtype 0 ≤ (b⁻).val at h
    simpa only [map_zero] using h
  obtain ⟨x, hx, hxn, hxp⟩ := modular_radon_nikodym_nonnegative Ω (b⁺).val (b⁺).property hp z hz
  obtain ⟨y, hy, hyn, hyp⟩ := modular_radon_nikodym_nonnegative Ω (b⁻).val (b⁻).property hn z hz
  have hpn : ‖(b⁺).val‖ ≤ ‖b‖ := CStarAlgebra.norm_posPart_le b
  have hnn : ‖(b⁻).val‖ ≤ ‖b‖ := CStarAlgebra.norm_negPart_le b
  refine ⟨x - y, hx.sub hy, ?_, ?_⟩
  · calc
      ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ (1 + ‖(b⁺).val‖) / z.re + (1 + ‖(b⁻).val‖) / z.re := add_le_add hxn hyn
      _ ≤ (1 + ‖b‖) / z.re + (1 + ‖b‖) / z.re := add_le_add
        (div_le_div_of_nonneg_right (add_le_add le_rfl hpn) hz.le)
        (div_le_div_of_nonneg_right (add_le_add le_rfl hnn) hz.le)
      _ = 2 * (1 + ‖b‖) / z.re := by ring
  · intro a
    have he : b.val = (b⁺).val - (b⁻).val :=
      congrArg Subtype.val (CFC.posPart_sub_negPart b hb).symm
    rw [he]
    change (inner ℂ (a.val.val Ω) (((b⁺).val - (b⁻).val) Ω)).re =
      (z * inner ℂ (a.val.val Ω) ((x.val - y.val) Ω)).re
    simp only [sub_apply, inner_sub_right, mul_sub, Complex.sub_re, hxp a, hyp a]

end

end KadisonKastler

end OAI
