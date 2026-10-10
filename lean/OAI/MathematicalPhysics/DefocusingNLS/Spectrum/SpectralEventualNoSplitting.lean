import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHolomorphicNoSplitting
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralKernelNormalization

namespace OAI

/-! Nonzero nearby kernels cannot split a simple limiting holomorphic root. -/

open Set Filter Topology
namespace DefocusingNLS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem spectral_eventual_no_splitting
    (F : ℕ → ℂ → E →L[ℂ] E) (f : ℂ → E →L[ℂ] E)
    (U : Set ℂ) (hU : IsOpen U)
    (hF : TendstoLocallyUniformlyOn F f atTop U)
    (hd : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) U)
    (z : ℂ) (hz : z ∈ U) (hcompact : IsCompactOperator (f z))
    (x y : ℕ → ℂ) (hx : Tendsto x atTop (𝓝 z)) (hy : Tendsto y atTop (𝓝 z))
    (hne : ∀ᶠ n in atTop, x n ≠ y n)
    (L : E →L[ℂ] ℂ) (c : ℝ) (hc : 0 < c)
    (hbase : ∀ w : E, L w=0 → c * ‖w‖ ≤ ‖w-f z w‖)
    (u₀ : E) (hu₀ : f z u₀=u₀) (hL₀ : L u₀=1)
    (u v : ℕ → E)
    (hu : ∀ᶠ n in atTop, F n (x n) (u n)=u n ∧ u n ≠ 0)
    (hv : ∀ᶠ n in atTop, F n (y n) (v n)=v n ∧ v n ≠ 0)
    (hno : ∀ w : E, w-f z w ≠ deriv f z u₀) : False := by
  have hdf := hF.differentiableOn hd hU
  have hj := spectral_locallyUniform_joint_tendsto F f U hU hF z hz
    (hdf.differentiableAt (hU.mem_nhds hz)).continuousAt
  have hK := hj.comp (tendsto_id.prodMk hx)
  have hJ := hj.comp (tendsto_id.prodMk hy)
  have heK : ∀ᶠ n in atTop, ‖F n (x n)-f z‖ ≤ c/2 := by
    have ht := tendsto_iff_norm_sub_tendsto_zero.mp hK
    exact (ht.eventually (gt_mem_nhds (half_pos hc))).mono (fun _ h => h.le)
  have heJ : ∀ᶠ n in atTop, ‖F n (y n)-f z‖ ≤ c/2 := by
    have ht := tendsto_iff_norm_sub_tendsto_zero.mp hJ
    exact (ht.eventually (gt_mem_nhds (half_pos hc))).mono (fun _ h => h.le)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (heK.and (heJ.and (hu.and hv)))
  let k := fun n => n+N
  have hk : Tendsto k atTop atTop := tendsto_add_atTop_nat N
  have hg (n : ℕ) := hN (n+N) (Nat.le_add_left N n)
  let a := fun n => (L (u (k n)))⁻¹ • u (k n)
  let b := fun n => (L (v (k n)))⁻¹ • v (k n)
  have ha (n : ℕ) : F (k n) (x (k n)) (a n)=a n ∧ L (a n)=1 := by
    apply spectral_normalize_kernel _ L _ (hg n).2.2.1.1
    exact spectral_kernel_functional_ne_zero (f z) _ L c hc hbase
      (hg n).1 _ (hg n).2.2.1.1 (hg n).2.2.1.2
  have hb (n : ℕ) : F (k n) (y (k n)) (b n)=b n ∧ L (b n)=1 := by
    apply spectral_normalize_kernel _ L _ (hg n).2.2.2.1
    exact spectral_kernel_functional_ne_zero (f z) _ L c hc hbase
      (hg n).2.1 _ (hg n).2.2.2.1 (hg n).2.2.2.2
  have hFk : TendstoLocallyUniformlyOn (fun n => F (k n)) f atTop U := by
    intro V hV w hw
    obtain ⟨S,hS,hFS⟩ := hF V hV w hw
    exact ⟨S,hS,hk.eventually hFS⟩
  exact spectral_holomorphic_no_splitting (fun n => F (k n)) f U hU
    hFk (hk.eventually hd) z hz hcompact
    (fun n => x (k n)) (fun n => y (k n)) (hx.comp hk) (hy.comp hk)
    (hk.eventually hne) L c hc hbase (fun n => (hg n).1) (fun n => (hg n).2.1)
    u₀ hu₀ hL₀ a b (fun n => (ha n).1) (fun n => (hb n).1)
    (fun n => (ha n).2) (fun n => (hb n).2) hno

end DefocusingNLS

end OAI
