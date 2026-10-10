import OAI.Analysis.KadisonKastler.ModularRadonNikodym
import OAI.Analysis.KadisonKastler.ModularPairingUniqueness

namespace OAI

/-! # The full right-half-plane parameter in the modular pairing equation -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

/-- Rescaling the normalized pairing keeps an explicit operator norm bound. -/
theorem modular_radon_nikodym_positive_halfPlane (Ω : H) (b : H →L[ℂ] H)
    (hb : b ∈ M.commutant) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (z : ℂ) (hz : 0 < z.re) :
    ∃ x : Algebra M, IsSelfAdjoint x ∧ ‖x‖ ≤ 1 / z.re ∧
      ∀ a : selfAdjoint (Algebra M),
        (inner ℂ (a.val.val Ω) (b Ω)).re =
          (z * inner ℂ (a.val.val Ω) (x.val Ω)).re := by
  let r : ℝ := z.re⁻¹
  have hr : 0 < r := inv_pos.mpr hz
  let w : ℂ := r • z
  have hw : w.re = 1 := by
    simpa only [w, Complex.smul_re, smul_eq_mul, r] using inv_mul_cancel₀ hz.ne'
  obtain ⟨x, hx, hxn, hxp⟩ := modular_radon_nikodym_positive Ω b hb hb0 hb1 w hw
  refine ⟨r • x, ?_, ?_, ?_⟩
  · change star (r • x) = r • x
    rw [star_smul, star_trivial, hx.star_eq]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    simpa only [r, one_div, mul_one] using mul_le_mul_of_nonneg_left hxn hr.le
  · intro a
    rw [hxp a]
    change (w * inner ℂ (a.val.val Ω) (x.val Ω)).re =
      (z * inner ℂ (a.val.val Ω) (r • x.val Ω)).re
    rw [← Complex.coe_smul r, inner_smul_right]
    rw [show w = (r : ℂ) * z from Complex.real_smul]
    change (((r : ℂ) * z) * inner ℂ (a.val.val Ω) (x.val Ω)).re =
      (z * ((r : ℂ) * inner ℂ (a.val.val Ω) (x.val Ω))).re
    congr 1
    ring

end

end KadisonKastler

end OAI
