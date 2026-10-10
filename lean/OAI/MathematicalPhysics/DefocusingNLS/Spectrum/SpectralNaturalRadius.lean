import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningRootRemote

namespace OAI

/-! Construct the natural remote radius; its escape follows from the
angular-dominated hypothesis rather than an additional radius assumption. -/

open Filter
namespace DefocusingNLS

noncomputable def spectralNaturalRadius (ell : ℕ) (omega : ℝ) : ℝ :=
  16*Real.sqrt (max ((ell : ℝ)+1) omega)

theorem spectralNaturalRadius_data (ell : ℕ) (omega : ℝ) :
    0 < spectralNaturalRadius ell omega ∧
    (spectralNaturalRadius ell omega)^2 = 256*max ((ell : ℝ)+1) omega := by
  have hs : 0 < max ((ell : ℝ)+1) omega :=
    lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨by dsimp only [spectralNaturalRadius]; positivity,?_⟩
  dsimp only [spectralNaturalRadius]
  rw [mul_pow,Real.sq_sqrt hs.le]
  norm_num

theorem spectralNaturalRadius_caseI_tendsto (ell : ℕ → ℕ) (b omega : ℕ → ℝ)
    (hdata : ∀ n, 0 ≤ b n ∧ b n ≤ 1 ∧ 0 ≤ omega n)
    (hescape : Tendsto (fun n => ((ell n : ℝ)*(ell n+10))/(1+omega n)) atTop atTop) :
    Tendsto (fun n => spectralNaturalRadius (ell n) (omega n)) atTop atTop := by
  let r := fun n => spectralTurningRoot 1 (b n) ((ell n : ℝ)*(ell n+10)) (omega n)
  have hr : ∀ n, 0 < r n ∧ homogeneousSpectralLocalizationFrequency 1 (b n)
      ((ell n : ℝ)*(ell n+10)) (omega n) (r n) = 0 := fun n =>
    spectralTurningRoot_data 1 _ _ _ (by positivity)
  have hrTop := spectralTurning_radius_escape_caseI 1 (by norm_num) b
    (fun n => (ell n : ℝ)*(ell n+10)) omega r hescape (Eventually.of_forall (fun n =>
      ⟨(hdata n).2.1,by positivity,(hdata n).2.2,(hr n).1,(hr n).2⟩))
  apply tendsto_atTop_mono _ hrTop
  intro n
  have hn := spectralNaturalRadius_data (ell n) (omega n)
  have hremote := spectralTurningRoot_remote (ell n) 1 (b n) (omega n)
    (spectralNaturalRadius (ell n) (omega n)) (by norm_num) (hdata n).1 (hdata n).2.2 hn.1 hn.2
  change r n ≤ _
  change 2*r n ≤ _ at hremote
  linarith [(hr n).1]

theorem spectralNaturalRadius_frequency_tendsto (ell : ℕ → ℕ) (omega : ℕ → ℝ)
    (hw : Tendsto omega atTop atTop) :
    Tendsto (fun n => spectralNaturalRadius (ell n) (omega n)) atTop atTop := by
  apply tendsto_atTop_mono _ (Real.tendsto_sqrt_atTop.comp hw)
  intro n
  have hm := Real.sqrt_le_sqrt (le_max_right ((ell n : ℝ)+1) (omega n))
  dsimp only [spectralNaturalRadius,Function.comp_def]
  nlinarith [Real.sqrt_nonneg (max ((ell n : ℝ)+1) (omega n))]

end DefocusingNLS

end OAI
