import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHolomorphicDifference
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNormalizedKernelLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCompactChainLimit

namespace OAI

/-! The local compact-pencil simplicity argument: normalized distinct roots
cannot approach a simple limiting root without producing a first chain. -/

open Set Filter Topology
namespace DefocusingNLS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem spectral_holomorphic_no_splitting
    (F : ℕ → ℂ → E →L[ℂ] E) (f : ℂ → E →L[ℂ] E)
    (U : Set ℂ) (hU : IsOpen U)
    (hF : TendstoLocallyUniformlyOn F f atTop U)
    (hd : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) U)
    (z : ℂ) (hz : z ∈ U) (hcompact : IsCompactOperator (f z))
    (x y : ℕ → ℂ) (hx : Tendsto x atTop (𝓝 z)) (hy : Tendsto y atTop (𝓝 z))
    (hne : ∀ᶠ n in atTop, x n ≠ y n)
    (L : E →L[ℂ] ℂ) (c : ℝ) (hc : 0 < c)
    (hbase : ∀ w : E, L w=0 → c * ‖w‖ ≤ ‖w-f z w‖)
    (hclosex : ∀ n, ‖F n (x n)-f z‖ ≤ c/2)
    (hclosey : ∀ n, ‖F n (y n)-f z‖ ≤ c/2)
    (u₀ : E) (hu₀ : f z u₀=u₀) (hL₀ : L u₀=1)
    (u v : ℕ → E) (hu : ∀ n, F n (x n) (u n)=u n)
    (hv : ∀ n, F n (y n) (v n)=v n)
    (hLu : ∀ n, L (u n)=1) (hLv : ∀ n, L (v n)=1)
    (hno : ∀ w : E, w-f z w ≠ deriv f z u₀) : False := by
  have hdf : DifferentiableOn ℂ f U := hF.differentiableOn hd hU
  have hj := spectral_locallyUniform_joint_tendsto F f U hU hF z hz
    (hdf.differentiableAt (hU.mem_nhds hz)).continuousAt
  have hK : Tendsto (fun n => F n (x n)) atTop (𝓝 (f z)) :=
    hj.comp (tendsto_id.prodMk hx)
  have hJ : Tendsto (fun n => F n (y n)) atTop (𝓝 (f z)) :=
    hj.comp (tendsto_id.prodMk hy)
  have hvlim := spectral_normalized_kernel_tendsto (fun n => F n (y n)) (f z)
    hJ L c hc hbase hclosey u₀ v hu₀ hv (fun n => (hLv n).trans hL₀.symm)
  have hD := spectral_holomorphic_divided_difference_tendsto F f U hU hF hd z hz x y hx hy hne
  exact compact_pencil_no_splitting (fun n => F n (x n)) (fun n => F n (y n))
    (fun n => (x n-y n)⁻¹ • (F n (x n)-F n (y n))) (f z) (deriv f z)
    hK hcompact hD L c hc hbase hclosex u v u₀ hvlim hu hv
    (fun n => (hLu n).trans (hLv n).symm) (fun n => x n-y n) (fun _ => rfl) hno

end DefocusingNLS

end OAI
