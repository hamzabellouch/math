import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralEventualNoJordan
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralEventualKernelLine

namespace OAI

/-! Geometric and analytic simplicity persist near a simple compact limiting pencil. -/

open Set Filter Topology
namespace DefocusingNLS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem spectral_eventually_simple
    (F : ℕ → ℂ → E →L[ℂ] E) (f : ℂ → E →L[ℂ] E)
    (U : Set ℂ) (hU : IsOpen U)
    (hF : TendstoLocallyUniformlyOn F f atTop U)
    (hd : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) U)
    (z : ℂ) (hz : z ∈ U) (hcompact : IsCompactOperator (f z))
    (x : ℕ → ℂ) (hx : Tendsto x atTop (𝓝 z))
    (hker : ∀ u₀ : E, u₀ ≠ 0 → f z u₀=u₀ →
      ∀ w : E, f z w=w → ∃ a : ℂ, w=a • u₀)
    (hno : ∀ u₀ : E, u₀ ≠ 0 → f z u₀=u₀ →
      ∀ w : E, w-f z w ≠ deriv f z u₀) :
    ∀ᶠ n in atTop,
      (∀ u v : E, F n (x n) u=u → u ≠ 0 → F n (x n) v=v → ∃ a : ℂ, v=a • u) ∧
      (∀ u v : E, F n (x n) u=u → u ≠ 0 →
        v-F n (x n) v ≠ deriv (F n) (x n) u) := by
  have hj := spectral_locallyUniform_joint_tendsto F f U hU hF z hz
    ((hF.differentiableOn hd hU).differentiableAt (hU.mem_nhds hz)).continuousAt
  exact (spectral_eventually_kernel_line (fun n => F n (x n)) (f z)
    (hj.comp (tendsto_id.prodMk hx)) hcompact hker).and
    (spectral_eventually_no_jordan F f U hU hF hd z hz hcompact x hx hker hno)

end DefocusingNLS

end OAI
