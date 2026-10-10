import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellGreenBounds

namespace OAI

/-! Convert the piecewise Green bound to both closed integration intervals.
At the diagonal the derivative jump contributes exactly one inverse weight. -/

open Set
namespace DefocusingNLS

theorem spectralGreen_diagonal_jump (D U : ℂ × ℂ) (W : ℂ) (hW : W ≠ 0)
    (hdet : spectralScalarWronskian D U = W) :
    (D.1/W) • U = (U.1/W) • D+(0,1) := by
  apply Prod.ext
  · change D.1/W*U.1 = U.1/W*D.1+0
    ring
  · change D.1/W*U.2 = U.1/W*D.2+1
    dsimp only [spectralScalarWronskian] at hdet
    field_simp
    linear_combination hdet

theorem spectralGreen_closed_branch_bounds
    (D U : ℝ → ℂ × ℂ) (W : ℂ) (k : ℝ → ℝ) (R E A kap r : ℝ)
    (hr : r ∈ Icc R E) (hA : 0 ≤ A) (hkap : 0 < kap)
    (hk : ∀ t ∈ Icc R E, kap ≤ k t) (hW : W ≠ 0)
    (hdet : spectralScalarWronskian (D r) (U r) = W)
    (hgreen : ∀ t ∈ Icc R E,
      spectralShellNorm (k r) (spectralScalarGreenState D U W r t) ≤ A/(k t)) :
    (∀ t ∈ Icc R r, spectralShellNorm (k r) (((D t).1/W) • U r) ≤ (A+1)/kap) ∧
      (∀ t ∈ Icc r E, spectralShellNorm (k r) (((U t).1/W) • D r) ≤ (A+1)/kap) := by
  have hkr : 0 < k r := hkap.trans_le (hk r hr)
  have hconst : A/kap ≤ (A+1)/kap := by gcongr; linarith
  constructor
  · intro t ht
    have htE : t ∈ Icc R E := ⟨ht.1,ht.2.trans hr.2⟩
    by_cases htr : t = r
    · subst t
      rw [spectralGreen_diagonal_jump (D r) (U r) W hW hdet]
      have hb := hgreen r hr
      rw [spectralScalarGreenState,ite_eq_left le_rfl] at hb
      calc
        _ ≤ spectralShellNorm (k r) (((U r).1/W) • D r)+spectralShellNorm (k r) (0,1) :=
          spectralShellNorm_add_le _ hkr.le _ _
        _ ≤ A/(k r)+(k r)⁻¹ := by
          simpa only [spectralShellNorm,norm_zero,mul_zero,norm_one,inv_mul_cancel₀,
            mul_one,zero_add] using add_le_add hb (le_refl ((k r)⁻¹))
        _ = (A+1)/(k r) := by ring
        _ ≤ (A+1)/kap := div_le_div_of_nonneg_left (by linarith) hkap (hk r hr)
    · have hrt : ¬r ≤ t := not_le.mpr (lt_of_le_of_ne ht.2 htr)
      have hb := hgreen t htE
      rw [spectralScalarGreenState,ite_eq_right hrt] at hb
      exact hb.trans ((div_le_div_of_nonneg_left hA hkap (hk t htE)).trans hconst)
  · intro t ht
    have htE : t ∈ Icc R E := ⟨hr.1.trans ht.1,ht.2⟩
    have hb := hgreen t htE
    rw [spectralScalarGreenState,ite_eq_left ht.1] at hb
    exact hb.trans ((div_le_div_of_nonneg_left hA hkap (hk t htE)).trans hconst)

end DefocusingNLS

end OAI
