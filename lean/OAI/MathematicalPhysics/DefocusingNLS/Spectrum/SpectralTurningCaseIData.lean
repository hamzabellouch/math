import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningRootRemote

namespace OAI

/-! Actual turning data for an angular-dominated parameter sequence. -/

open Filter Topology
namespace DefocusingNLS

theorem spectralTurningRoot_caseI_data
    (ell : ℕ → ℕ) (h : ℝ) (b omega gamma E : ℕ → ℝ)
    (hh : h^2 = 1)
    (hescape : Tendsto (fun n => ((ell n : ℝ)*(ell n+10))/(1+omega n)) atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 ≤ b n ∧ b n ≤ 1 ∧ 0 ≤ omega n ∧
      |gamma n| ≤ 8 ∧ 0 < E n ∧ (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n)) :
    let r₀ := fun n => spectralTurningRoot h (b n) ((ell n : ℝ)*(ell n+10)) (omega n)
    let d := fun n => spectralTurningRootScale ((ell n : ℝ)*(ell n+10)) (r₀ n)
    Tendsto r₀ atTop atTop ∧ Tendsto d atTop (𝓝 0) ∧
      (∀ n, 0 < d n) ∧
      ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ b n ∧ b n ≤ 1 ∧
        |gamma n| ≤ 8 ∧ 2*r₀ n ≤ E n ∧
        (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n) ∧
        homogeneousSpectralLocalizationFrequency h (b n)
          ((ell n : ℝ)*(ell n+10)) (omega n) (r₀ n) = 0 ∧
        spectralLiouvilleSlope ((ell n : ℝ)*(ell n+10)) (r₀ n)*(d n)^3 = 1 := by
  dsimp only
  let r₀ := fun n => spectralTurningRoot h (b n) ((ell n : ℝ)*(ell n+10)) (omega n)
  let d := fun n => spectralTurningRootScale ((ell n : ℝ)*(ell n+10)) (r₀ n)
  have hr : ∀ n, 0 < r₀ n ∧ homogeneousSpectralLocalizationFrequency h (b n)
      ((ell n : ℝ)*(ell n+10)) (omega n) (r₀ n) = 0 := fun n =>
    spectralTurningRoot_data h (b n) ((ell n : ℝ)*(ell n+10)) (omega n) (by positivity)
  have hd : ∀ n, 0 < d n ∧ spectralLiouvilleSlope ((ell n : ℝ)*(ell n+10))
      (r₀ n)*(d n)^3 = 1 := fun n =>
    spectralTurningRootScale_data _ _ (by positivity) (hr n).1
  have hha : |h| ≤ 1 := by
    rcases sq_eq_one_iff.mp hh with rfl | rfl <;> norm_num
  have hrTop : Tendsto r₀ atTop atTop := spectralTurning_radius_escape_caseI h hha b
    (fun n => (ell n : ℝ)*(ell n+10)) omega r₀ hescape (by
      filter_upwards [hdata] with n hn
      exact ⟨hn.2.1,by positivity,hn.2.2.1,(hr n).1,(hr n).2⟩)
  have hd0 : Tendsto d atTop (𝓝 0) := spectralTurningScale_tendsto
    (fun n => (ell n : ℝ)*(ell n+10)) r₀ d hrTop (Eventually.of_forall (fun n =>
      ⟨(hr n).1,(hd n).1.le,by positivity,(hd n).2⟩))
  refine ⟨hrTop,hd0,fun n => (hd n).1,?_⟩
  filter_upwards [hdata] with n hn
  exact ⟨(hr n).1,(hd n).1.le,hn.1,hn.2.1,hn.2.2.2.1,
    spectralTurningRoot_remote (ell n) h (b n) (omega n) (E n) hha hn.1 hn.2.2.1
      hn.2.2.2.2.1 hn.2.2.2.2.2,hn.2.2.2.2.2,(hr n).2,(hd n).2⟩

end DefocusingNLS

end OAI
