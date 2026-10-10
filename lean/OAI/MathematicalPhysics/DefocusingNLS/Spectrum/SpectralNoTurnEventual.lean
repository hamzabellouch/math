import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnTransfer
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnErrorLimit

namespace OAI

/-! All numerical prerequisites for the no-turn outgoing comparison hold
eventually for the actual frequency-dominated parameter sequence. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralNoTurn_eventual_data
    (ell : ℕ → ℕ) (b omega gamma E : ℕ → ℝ) (C R : ℝ)
    (hC : 0 ≤ C) (hR : 0 < R) (hw : Tendsto omega atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 ≤ b n ∧ |gamma n| ≤ 8 ∧ 0 < E n ∧
      (ell n : ℝ)*(ell n+10)+99/4 ≤ C*omega n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n)) :
    (Tendsto E atTop atTop) ∧ ∀ᶠ n in atTop,
      0 < omega n ∧ C ≤ omega n ∧ R ≤ E n ∧
      (E n)^2 = 256*omega n ∧ E n ≤ 32*Real.sqrt (omega n/2) ∧
      2/R+4*C/R^3 ≤ 2*Real.sqrt (omega n/2) ∧
      spectralNoTurnBranchError C R (omega n) (E n) ≤ Real.exp (-256)/2 := by
  have hE : Tendsto E atTop atTop := by
    apply tendsto_atTop_mono' atTop _ (Real.tendsto_sqrt_atTop.comp hw)
    filter_upwards [hdata,hw.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hwn
    have he := hn.2.2.2.2
    have hm : omega n ≤ max ((ell n : ℝ)+1) (omega n) := le_max_right _ _
    have hs := Real.sq_sqrt hwn.le
    have hs0 := Real.sqrt_nonneg (omega n)
    change Real.sqrt (omega n) ≤ E n
    nlinarith [hn.2.2.1]
  have herr := spectralNoTurn_branch_error_tendsto omega E C R hw hE
  have hroot : Tendsto (fun n => Real.sqrt (omega n/2)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (hw.atTop_div_const (by norm_num))
  refine ⟨hE,?_⟩
  filter_upwards [hdata,hw.eventually (eventually_ge_atTop (C+2)),
    hw.eventually (eventually_ge_atTop (R^2)),
    hroot.eventually (eventually_ge_atTop ((2/R+4*C/R^3)/2)),
    herr.eventually (gt_mem_nhds (half_pos (Real.exp_pos (-256))))]
    with n hn hcn hrn hkn hen
  have hwn : 0 < omega n := by linarith
  have hdom : (ell n : ℝ)+1 ≤ omega n := by
    by_contra hh
    have hgt : omega n-1 < (ell n : ℝ) := by linarith
    have hell : 0 ≤ (ell n : ℝ) := Nat.cast_nonneg _
    have hsq : (omega n-1)^2 < (ell n : ℝ)^2 := by nlinarith
    have hm := mul_nonneg hwn.le (sub_nonneg.mpr hcn)
    nlinarith [hn.2.2.2.1]
  have he := spectralNoTurn_remote (ell n) (omega n) C R (E n) hC hcn hR hrn
    hn.2.2.2.1 hn.2.2.1 hn.2.2.2.2
  exact ⟨hwn,by linarith,he.1,by simpa only [max_eq_right hdom] using hn.2.2.2.2,
    he.2,by linarith,hen.le⟩

end DefocusingNLS

end OAI
