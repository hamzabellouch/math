import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteLeadingSymbol

namespace OAI

/-! The remote radius chosen in the paper supplies the uniform smallness
and derivative bounds used by the constructed block reduction. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralRemote_parameter_bounds (ell : ℕ) (omega S R : ℝ)
    (hw : 0 ≤ omega) (heS : (ell : ℝ)+1 ≤ S) (hwS : omega ≤ S)
    (hR : 0 < R) (hRS : 64*S ≤ R^2) :
    |omega| *Real.exp (-2*Real.log R) ≤ 1/64 ∧
      |(ell : ℝ)*(ell+10)| *Real.exp (-4*Real.log R) ≤ 1/256 := by
  have hS : 0 ≤ S := by linarith [Nat.cast_nonneg (α := ℝ) ell]
  have he : 0 ≤ (ell : ℝ) := Nat.cast_nonneg ell
  have hη : (ell : ℝ)*(ell+10) ≤ 16*S^2 := by
    have hs := (sq_le_sq₀ (by positivity : 0 ≤ (ell : ℝ)+1) hS).mpr heS
    nlinarith
  have hsquare : S^2 ≤ (R^2/64)^2 :=
    (sq_le_sq₀ hS (by positivity)).mpr (by linarith)
  have hr2 := sq_pos_of_pos hR
  have hr4 := pow_pos hR 4
  have hb2 : omega/R^2 ≤ 1/64 := (div_le_iff₀ hr2).mpr (by linarith)
  have hb4 : ((ell : ℝ)*(ell+10))/R^4 ≤ 1/256 :=
    (div_le_iff₀ hr4).mpr (by nlinarith)
  have hexp (k : ℕ) : Real.exp (-(k : ℝ)*Real.log R) = (R^k)⁻¹ := by
    rw [neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log hR]
  rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num,hexp 2,
    show (-4 : ℝ) = -(4 : ℕ) by norm_num,hexp 4]
  rw [abs_of_nonneg hw,abs_of_nonneg (by positivity : 0 ≤ (ell : ℝ)*(ell+10)),← div_eq_mul_inv,
    ← div_eq_mul_inv]
  exact ⟨hb2,hb4⟩

theorem spectralRemote_scale_symbols
    (ell : ℕ → ℕ) (omega S R : ℕ → ℝ)
    (hdata : ∀ᶠ n in atTop, 0 ≤ omega n ∧ (ell n : ℝ)+1 ≤ S n ∧ omega n ≤ S n ∧
      0 < R n ∧ 64*S n ≤ (R n)^2) :
    HasUniformLogJetBound (fun n => Real.log (R n)) 0
      (spectralRemoteLeadingCoefficient omega (fun n => (ell n : ℝ)*(ell n+10))) ∧
    (∀ᶠ n in atTop, ∀ t ∈ Ioi (Real.log (R n)), ∀ i,
      |spectralRemoteLeadingCoefficient omega (fun n => (ell n : ℝ)*(ell n+10)) n t i| ≤ 1/32) := by
  have hb := hdata.mono (fun n hn => spectralRemote_parameter_bounds (ell n)
    (omega n) (S n) (R n) hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2)
  exact ⟨spectralRemote_leading_coefficient_symbol (hb.mono (fun _ hn => hn.1))
    (hb.mono (fun _ hn => hn.2)),
    spectralRemote_leading_coefficient_small (hb.mono (fun _ hn => hn.1))
      (hb.mono (fun _ hn => hn.2))⟩

end DefocusingNLS

end OAI
