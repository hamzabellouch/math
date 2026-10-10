import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPhysicalCharacter
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! # Spatial differences of the physical Fourier characters -/

open scoped RealInnerProductSpace

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem complex_phase_lipschitz (s t : ℝ) :
    ‖Complex.exp ((t : ℂ) * Complex.I) - Complex.exp ((s : ℂ) * Complex.I)‖ ≤ |t - s| := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I))
      (Complex.exp ((x : ℂ) * Complex.I) * Complex.I) x := by
    simpa only [id_eq, Complex.ofReal_one, one_mul] using
      (((hasDerivAt_id x).ofReal_comp.mul_const Complex.I).cexp)
  have hb (x : ℝ) : ‖Complex.exp ((x : ℂ) * Complex.I) * Complex.I‖ ≤ (1 : ℝ) := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_I, one_mul]
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_ : x ∈ (Set.univ : Set ℝ)) => (hd x).hasDerivWithinAt)
    (fun x _ => hb x) (convex_univ : Convex ℝ (Set.univ : Set ℝ))
    (Set.mem_univ s) (Set.mem_univ t)
  simpa only [one_mul, Real.norm_eq_abs] using he

theorem spatialFourierCharacter_lipschitz (n : frequencyLattice) (x y : E) :
    ‖spatialFourierCharacter n x - spatialFourierCharacter n y‖ ≤ ‖n‖ * ‖x - y‖ := by
  have h := complex_phase_lipschitz ⟪y, (n : E)⟫ ⟪x, (n : E)⟫
  rw [← inner_sub_left] at h
  exact h.trans ((abs_real_inner_le_norm (x - y) (n : E)).trans_eq (mul_comm _ _))

theorem scaledFourierCharacter_lipschitz (L : ℝ) (hL : 0 < L) (n : frequencyLattice) (x y : E) :
    ‖spatialFourierCharacter n (L⁻¹ • x) - spatialFourierCharacter n (L⁻¹ • y)‖ ≤
      (‖n‖ / L) * ‖x - y‖ := by
  have h := spatialFourierCharacter_lipschitz n (L⁻¹ • x) (L⁻¹ • y)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)] at h
  convert h using 1
  ring

end DefocusingNLS

end OAI
