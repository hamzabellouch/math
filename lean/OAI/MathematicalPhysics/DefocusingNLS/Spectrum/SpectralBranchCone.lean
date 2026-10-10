import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellNorm

namespace OAI

/-! A small weighted error around a graph branch controls both the value
and its Robin residual. -/

namespace DefocusingNLS

theorem spectralBranch_value_residual (k C A delta : ℝ) (hk : 0 < k) (hC : 0 ≤ C)
    (z L : ℂ) (D q : ℂ × ℂ) (hD : D.2 = L*D.1)
    (hA : k*‖D.1‖ = A) (hL : ‖L‖ ≤ C*k^2)
    (hclose : spectralShellNorm k (q-z • D) ≤ delta) :
    ‖z‖*A-delta ≤ k*‖q.1‖ ∧
      ‖q.2-L*q.1‖ ≤ (1+C)*k*delta := by
  let e := q-z • D
  have hd : 0 ≤ delta := (spectralShellNorm_nonneg k hk.le _).trans hclose
  have hval : ‖e.1‖ ≤ delta/k :=
    (spectralShellNorm_value k hk e).trans (div_le_div_of_nonneg_right hclose hk.le)
  have hder : ‖e.2‖ ≤ k*delta :=
    (spectralShellNorm_slope k hk e).trans (mul_le_mul_of_nonneg_left hclose hk.le)
  have hfirst : ‖z*D.1‖ ≤ ‖q.1‖+‖e.1‖ := by
    have he : z*D.1 = q.1-e.1 := by
      dsimp only [e,Prod.fst_sub,Prod.smul_fst,smul_eq_mul]
      ring
    rw [he]
    exact norm_sub_le _ _
  have hmult := mul_le_mul_of_nonneg_left hfirst hk.le
  have hscaled : k*‖z*D.1‖ = ‖z‖*A := by rw [norm_mul,← hA]; ring
  have hvalscaled : k*‖e.1‖ ≤ delta := by
    simpa only [mul_comm] using (le_div_iff₀ hk).mp hval
  refine ⟨by rw [hscaled] at hmult; nlinarith,?_⟩
  have he : q.2-L*q.1 = e.2-L*e.1 := by
    dsimp only [e,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    rw [hD]
    ring
  rw [he]
  calc
    _ ≤ ‖e.2‖+‖L‖*‖e.1‖ := by simpa only [norm_mul] using norm_sub_le e.2 (L*e.1)
    _ ≤ k*delta+(C*k^2)*(delta/k) := by gcongr
    _ = (1+C)*k*delta := by field_simp

end DefocusingNLS

end OAI
