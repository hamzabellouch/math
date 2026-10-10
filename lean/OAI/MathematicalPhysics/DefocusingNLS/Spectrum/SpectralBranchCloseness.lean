import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellNorm

namespace OAI

/-! A small weighted error from a nonzero scalar branch gives a nonzero
value and a quantitative logarithmic derivative estimate. -/

namespace DefocusingNLS

theorem spectralBranch_value_lower (k c eps : ℝ) (hk : 0 < k) (hc : 0 < c)
    (heps : eps ≤ c/2) (q D : ℂ × ℂ) (z : ℂ)
    (hD : k*‖D.1‖ = 1) (hz : c ≤ ‖z‖)
    (herr : spectralShellNorm k (q-z • D) ≤ eps) :
    c/2 ≤ k*‖q.1‖ ∧ q.1 ≠ 0 := by
  have hv := (spectralShellNorm_value k hk (q-z • D)).trans
    (div_le_div_of_nonneg_right herr hk.le)
  have ht : ‖z*D.1‖ ≤ ‖q.1‖+‖q.1-z*D.1‖ := by
    calc
      _ = ‖q.1-(q.1-z*D.1)‖ := by congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  have he : k*‖z*D.1‖ = ‖z‖ := by rw [norm_mul]; nlinarith [hD]
  have he' := mul_le_mul_of_nonneg_left ht hk.le
  have hve : k*‖q.1-z*D.1‖ ≤ eps := by
    change ‖q.1-z*D.1‖ ≤ eps/k at hv
    simpa only [mul_comm] using (le_div_iff₀ hk).mp hv
  have hlow : c/2 ≤ k*‖q.1‖ := by nlinarith
  refine ⟨hlow,?_⟩
  intro hq
  rw [hq,norm_zero,mul_zero] at hlow
  linarith

theorem spectralBranch_slope_residual (k B eps : ℝ) (hk : 0 < k) (hB : 0 ≤ B)
    (_heps : 0 ≤ eps) (q D : ℂ × ℂ) (z L : ℂ)
    (hD : D.2 = L*D.1) (hL : ‖L‖ ≤ B*k^2)
    (herr : spectralShellNorm k (q-z • D) ≤ eps) :
    ‖q.2-L*q.1‖ ≤ (1+B)*k*eps := by
  let e := q-z • D
  have he1 : ‖e.1‖ ≤ eps/k := (spectralShellNorm_value k hk e).trans
    (div_le_div_of_nonneg_right herr hk.le)
  have he2 : ‖e.2‖ ≤ k*eps := (spectralShellNorm_slope k hk e).trans
    (mul_le_mul_of_nonneg_left herr hk.le)
  have hid : q.2-L*q.1 = e.2-L*e.1 := by dsimp only [e,Prod.snd_sub,Prod.fst_sub,Prod.smul_snd,Prod.smul_fst,smul_eq_mul]; rw [hD]; ring
  rw [hid]
  calc
    _ ≤ ‖e.2‖+‖L*e.1‖ := norm_sub_le _ _
    _ = ‖e.2‖+‖L‖*‖e.1‖ := by rw [norm_mul]
    _ ≤ k*eps+(B*k^2)*(eps/k) := add_le_add he2 (mul_le_mul hL he1 (norm_nonneg _) (by positivity))
    _ = _ := by field_simp

theorem spectralBranch_logarithmic_bound (k B c eps : ℝ) (hk : 0 < k) (hB : 0 ≤ B)
    (hc : 0 < c) (heps : 0 ≤ eps) (heps' : eps ≤ c/2) (q D : ℂ × ℂ) (z L : ℂ)
    (hDn : k*‖D.1‖ = 1) (hz : c ≤ ‖z‖)
    (hD : D.2 = L*D.1) (hL : ‖L‖ ≤ B*k^2)
    (herr : spectralShellNorm k (q-z • D) ≤ eps) :
    q.1 ≠ 0 ∧ ‖q.2/q.1-L‖ ≤ (2*(1+B)*eps/c)*k^2 := by
  obtain ⟨hlo,hq⟩ := spectralBranch_value_lower k c eps hk hc heps' q D z hDn hz herr
  have hres := spectralBranch_slope_residual k B eps hk hB heps q D z L hD hL herr
  refine ⟨hq,?_⟩
  have hid : q.2/q.1-L = (q.2-L*q.1)/q.1 := by field_simp
  rw [hid,norm_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr hq)).mpr
  apply hres.trans
  have hh := mul_le_mul_of_nonneg_left hlo (show 0 ≤ 2*(1+B)*eps*k/c by positivity)
  have heq : (2*(1+B)*eps*k/c)*(c/2) = (1+B)*k*eps := by field_simp
  rw [heq] at hh
  convert hh using 1
  ring

end DefocusingNLS

end OAI
