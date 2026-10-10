import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralEventualNoSplitting
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNonzeroKernelLimit
import Mathlib.Analysis.Normed.Module.HahnBanach

namespace OAI

/-! A one-dimensional limiting kernel with no first chain prevents distinct nearby roots. -/

open Set Filter Topology
namespace DefocusingNLS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem spectral_simple_limit_no_splitting
    (F : ℕ → ℂ → E →L[ℂ] E) (f : ℂ → E →L[ℂ] E)
    (U : Set ℂ) (hU : IsOpen U)
    (hF : TendstoLocallyUniformlyOn F f atTop U)
    (hd : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) U)
    (z : ℂ) (hz : z ∈ U) (hcompact : IsCompactOperator (f z))
    (x y : ℕ → ℂ) (hx : Tendsto x atTop (𝓝 z)) (hy : Tendsto y atTop (𝓝 z))
    (hne : ∀ᶠ n in atTop, x n ≠ y n)
    (u v : ℕ → E)
    (hu : ∀ᶠ n in atTop, F n (x n) (u n)=u n ∧ u n ≠ 0)
    (hv : ∀ᶠ n in atTop, F n (y n) (v n)=v n ∧ v n ≠ 0)
    (hker : ∀ u₀ : E, u₀ ≠ 0 → f z u₀=u₀ →
      ∀ w : E, f z w=w → ∃ a : ℂ, w=a • u₀)
    (hno : ∀ u₀ : E, u₀ ≠ 0 → f z u₀=u₀ →
      ∀ w : E, w-f z w ≠ deriv f z u₀) : False := by
  have hdf := hF.differentiableOn hd hU
  have hj := spectral_locallyUniform_joint_tendsto F f U hU hF z hz
    (hdf.differentiableAt (hU.mem_nhds hz)).continuousAt
  obtain ⟨u₀,hnorm,hfix⟩ := compact_kernel_limit_of_eventually_nonzero
    (fun n => F n (x n)) (f z) (hj.comp (tendsto_id.prodMk hx)) hcompact u hu
  have hu₀ : u₀ ≠ 0 := by
    intro he
    rw [he,norm_zero] at hnorm
    norm_num at hnorm
  obtain ⟨L,_hLnorm,hLu⟩ := exists_dual_vector ℂ u₀ (by rw [hnorm]; norm_num)
  have hL₀ : L u₀=1 := by simpa [hnorm] using hLu
  obtain ⟨c,hc,hbase⟩ := compact_simple_kernel_estimate (f z) hcompact u₀ L
    (by rw [hL₀]; norm_num) (hker u₀ hu₀ hfix)
  exact spectral_eventual_no_splitting F f U hU hF hd z hz hcompact x y hx hy hne
    L c hc hbase u₀ hfix hL₀ u v hu hv (hno u₀ hu₀ hfix)

end DefocusingNLS

end OAI
