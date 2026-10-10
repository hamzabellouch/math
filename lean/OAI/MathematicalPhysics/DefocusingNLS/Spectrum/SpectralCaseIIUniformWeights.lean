import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCaseIIWeightBounds
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningComparison
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningOuterWeight
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningScaleLimit

namespace OAI

/-! The actual two scalar Green weights have a common frequency scale on
the fixed shell. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralCaseII_uniform_weights
    (ell : ℕ → ℕ) (b omega gamma rp dp E : ℕ → ℝ) (C R B : ℝ)
    (hC : 0 ≤ C) (hR : 0 < R) (_hRB : R ≤ B) (hCR : 2*C ≤ R^2)
    (hw : Tendsto omega atTop atTop) (hrp : Tendsto rp atTop atTop)
    (hp : SpectralTurningFamilyData ell 1 b omega gamma rp dp E)
    (hang : ∀ᶠ n in atTop, (ell n : ℝ)*(ell n+10)+99/4 ≤ C*omega n) :
    ∀ᶠ n in atTop, ∀ r ∈ Icc R B,
      (Real.sqrt (omega n)/2 ≤ (spectralTurningRegularizedWeight 1 (b n)
        ((ell n : ℝ)*(ell n+10)) (omega n) (gamma n) (dp n) r)^2 ∧
        (spectralTurningRegularizedWeight 1 (b n) ((ell n : ℝ)*(ell n+10))
          (omega n) (gamma n) (dp n) r)^2 ≤ (C/R^2+11)*Real.sqrt (omega n)) ∧
      (Real.sqrt (omega n)/2 ≤ (Real.sqrt ‖spectralLiouvilleMomentum 1 (-1) (b n)
        ((ell n : ℝ)*(ell n+10)) (omega n) (-gamma n) r‖)^2 ∧
        (Real.sqrt ‖spectralLiouvilleMomentum 1 (-1) (b n) ((ell n : ℝ)*(ell n+10))
          (omega n) (-gamma n) r‖)^2 ≤ (C/R^2+11)*Real.sqrt (omega n)) := by
  have hddata : ∀ᶠ n in atTop, 0 < rp n ∧ 0 ≤ dp n ∧
      0 ≤ (ell n : ℝ)*(ell n+10) ∧ |gamma n| ≤ 8 ∧
      homogeneousSpectralLocalizationFrequency 1 (b n) ((ell n : ℝ)*(ell n+10)) (omega n) (rp n) = 0 ∧
      spectralLiouvilleSlope ((ell n : ℝ)*(ell n+10)) (rp n)*(dp n)^3 = 1 := by
    filter_upwards [hp] with n hn
    exact ⟨hn.1,hn.2.1,by positivity,hn.2.2.2.2.1,hn.2.2.2.2.2.2.2.1,hn.2.2.2.2.2.2.2.2⟩
  have hd := spectralTurningScale_tendsto (fun n => (ell n : ℝ)*(ell n+10)) rp dp hrp
    (hddata.mono (fun _ hn => ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.2.2⟩))
  have hout := spectralTurning_regularized_outer_weights 1 b
    (fun n => (ell n : ℝ)*(ell n+10)) omega gamma rp dp 2 8 (by norm_num) hrp hddata
  filter_upwards [hp,hang,hout,hrp.eventually (eventually_ge_atTop (B+2)),
    hd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hw.eventually (eventually_ge_atTop (2*(B^2/16+1)))] with n hn ha ho hr hd hw
  intro r hrr
  have hwr := ho.1 r (hR.trans_le hrr.1) (by linarith [hrr.2])
  have hb := spectralCaseII_momentum_bounds (b n) ((ell n : ℝ)*(ell n+10)) (omega n)
    (gamma n) C R B r hn.2.2.1 hn.2.2.2.1 (by positivity) hC hR hrr.1 hrr.2 hw ha hCR hn.2.2.2.2.1
  rw [hwr,Real.sq_sqrt (norm_nonneg _),Real.sq_sqrt (norm_nonneg _)]
  exact hb

end DefocusingNLS

end OAI
