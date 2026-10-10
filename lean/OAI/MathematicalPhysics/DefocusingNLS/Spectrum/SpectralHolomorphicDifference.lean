import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralDividedDifferenceLimit
import Mathlib.Analysis.Complex.LocallyUniformLimit

namespace OAI

/-! Locally uniform holomorphic convergence supplies the derivative convergence
needed for moving spectral divided differences. -/

open Set Filter Topology
namespace DefocusingNLS
variable {E : Type*} [NormedAddCommGroup E]

theorem spectral_locallyUniform_joint_tendsto
    (F : ℕ → ℂ → E) (f : ℂ → E) (U : Set ℂ) (hU : IsOpen U)
    (hF : TendstoLocallyUniformlyOn F f atTop U)
    (z : ℂ) (hz : z ∈ U) (hf : ContinuousAt f z) :
    Tendsto (fun p : ℕ × ℂ => F p.1 p.2) (atTop ×ˢ 𝓝 z) (𝓝 (f z)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hlocal := (tendstoLocallyUniformlyOn_iff_filter.mp hF) z hz
  rw [hU.nhdsWithin_eq hz] at hlocal
  have herror := Metric.tendstoUniformlyOnFilter_iff.mp hlocal (ε/2) (half_pos hε)
  have hp : Tendsto (fun p : ℕ × ℂ => f p.2) (atTop ×ˢ 𝓝 z) (𝓝 (f z)) :=
    hf.tendsto.comp tendsto_snd
  have hcont := Metric.tendsto_nhds.mp hp (ε/2) (half_pos hε)
  filter_upwards [herror,hcont] with p he hc
  have hc' : dist (f p.2) (f z) < ε/2 := hc
  calc
    dist (F p.1 p.2) (f z) ≤ dist (F p.1 p.2) (f p.2) + dist (f p.2) (f z) :=
      dist_triangle _ _ _
    _ < ε/2+ε/2 := add_lt_add (by simpa only [dist_comm] using he) hc'
    _ = ε := add_halves ε

variable [NormedSpace ℂ E] [CompleteSpace E]

theorem spectral_holomorphic_divided_difference_tendsto
    (F : ℕ → ℂ → E) (f : ℂ → E) (U : Set ℂ) (hU : IsOpen U)
    (hF : TendstoLocallyUniformlyOn F f atTop U)
    (hd : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) U)
    (z : ℂ) (hz : z ∈ U)
    (x y : ℕ → ℂ) (hx : Tendsto x atTop (𝓝 z)) (hy : Tendsto y atTop (𝓝 z))
    (hne : ∀ᶠ n in atTop, x n ≠ y n) :
    Tendsto (fun n => (x n-y n)⁻¹ • (F n (x n)-F n (y n)))
      atTop (𝓝 (deriv f z)) := by
  have hdf : DifferentiableOn ℂ f U := hF.differentiableOn hd hU
  have hderiv := hF.deriv hd hU
  have hj := spectral_locallyUniform_joint_tendsto (fun n => deriv (F n)) (deriv f)
    U hU hderiv z hz ((hdf.deriv hU).continuousOn.continuousAt (hU.mem_nhds hz))
  apply spectral_divided_difference_tendsto F (fun n => deriv (F n)) U hU z hz
    (deriv f z) _ hj x y hx hy hne
  filter_upwards [hd] with n hn w hw
  exact (hn.differentiableAt (hU.mem_nhds hw)).hasDerivAt

end DefocusingNLS

end OAI
