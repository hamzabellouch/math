import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningCaseIData
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningComparison

namespace OAI

/-! The positive channel turns and its Airy scale shrinks in Case II. -/

open Filter Topology
namespace DefocusingNLS

theorem spectralTurningRoot_caseII_data
    (ell : ℕ → ℕ) (b omega gamma E : ℕ → ℝ)
    (hw : Tendsto omega atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 ≤ b n ∧ b n ≤ 1 ∧ 0 ≤ omega n ∧
      |gamma n| ≤ 8 ∧ 0 < E n ∧ (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n)) :
    let r₀ := fun n => spectralTurningRoot 1 (b n) ((ell n : ℝ)*(ell n+10)) (omega n)
    let d := fun n => spectralTurningRootScale ((ell n : ℝ)*(ell n+10)) (r₀ n)
    Tendsto r₀ atTop atTop ∧ Tendsto d atTop (𝓝 0) ∧
      (∀ n, 0 < d n) ∧ SpectralTurningFamilyData ell 1 b omega gamma r₀ d E := by
  dsimp only
  let r₀ := fun n => spectralTurningRoot 1 (b n) ((ell n : ℝ)*(ell n+10)) (omega n)
  let d := fun n => spectralTurningRootScale ((ell n : ℝ)*(ell n+10)) (r₀ n)
  have hr : ∀ n, 0 < r₀ n ∧ homogeneousSpectralLocalizationFrequency 1 (b n)
      ((ell n : ℝ)*(ell n+10)) (omega n) (r₀ n) = 0 := fun n =>
    spectralTurningRoot_data 1 (b n) ((ell n : ℝ)*(ell n+10)) (omega n) (by positivity)
  have hd : ∀ n, 0 < d n ∧ spectralLiouvilleSlope ((ell n : ℝ)*(ell n+10))
      (r₀ n)*(d n)^3 = 1 := fun n =>
    spectralTurningRootScale_data _ _ (by positivity) (hr n).1
  have hrTop : Tendsto r₀ atTop atTop := spectralTurning_radius_escape_caseII b
    (fun n => (ell n : ℝ)*(ell n+10)) omega r₀ hw (by
      filter_upwards [hdata] with n hn
      exact ⟨hn.2.1,by positivity,(hr n).1,(hr n).2⟩)
  have hd0 : Tendsto d atTop (𝓝 0) := spectralTurningScale_tendsto
    (fun n => (ell n : ℝ)*(ell n+10)) r₀ d hrTop (Eventually.of_forall (fun n =>
      ⟨(hr n).1,(hd n).1.le,by positivity,(hd n).2⟩))
  refine ⟨hrTop,hd0,fun n => (hd n).1,?_⟩
  filter_upwards [hdata] with n hn
  exact ⟨(hr n).1,(hd n).1.le,hn.1,hn.2.1,hn.2.2.2.1,
    spectralTurningRoot_remote (ell n) 1 (b n) (omega n) (E n) (by norm_num) hn.1 hn.2.2.1
      hn.2.2.2.2.1 hn.2.2.2.2.2,hn.2.2.2.2.2,(hr n).2,(hd n).2⟩

end DefocusingNLS

end OAI
