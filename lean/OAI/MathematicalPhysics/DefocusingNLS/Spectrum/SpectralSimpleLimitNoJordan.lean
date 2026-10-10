import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSimpleLimitNoSplitting
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCompactJordanLimit

namespace OAI

/-! First analytic chains cannot persist near a simple limiting root. -/

open Set Filter Topology
namespace DefocusingNLS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem spectral_simple_limit_no_jordan
    (F : ℕ → ℂ → E →L[ℂ] E) (f : ℂ → E →L[ℂ] E)
    (U : Set ℂ) (hU : IsOpen U)
    (hF : TendstoLocallyUniformlyOn F f atTop U)
    (hd : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) U)
    (z : ℂ) (hz : z ∈ U) (hcompact : IsCompactOperator (f z))
    (x : ℕ → ℂ) (hx : Tendsto x atTop (𝓝 z)) (u v : ℕ → E)
    (hu : ∀ᶠ n in atTop, F n (x n) (u n)=u n ∧ u n ≠ 0)
    (hv : ∀ᶠ n in atTop, v n-F n (x n) (v n)=deriv (F n) (x n) (u n))
    (hker : ∀ u₀ : E, u₀ ≠ 0 → f z u₀=u₀ →
      ∀ w : E, f z w=w → ∃ a : ℂ, w=a • u₀)
    (hno : ∀ u₀ : E, u₀ ≠ 0 → f z u₀=u₀ →
      ∀ w : E, w-f z w ≠ deriv f z u₀) : False := by
  have hdf := hF.differentiableOn hd hU
  have hj := spectral_locallyUniform_joint_tendsto F f U hU hF z hz
    (hdf.differentiableAt (hU.mem_nhds hz)).continuousAt
  have hK := hj.comp (tendsto_id.prodMk hx)
  have hdj := spectral_locallyUniform_joint_tendsto (fun n => deriv (F n)) (deriv f)
    U hU (hF.deriv hd hU) z hz ((hdf.deriv hU).continuousOn.continuousAt (hU.mem_nhds hz))
  have hD := hdj.comp (tendsto_id.prodMk hx)
  obtain ⟨u₀,hnorm,hfix⟩ := compact_kernel_limit_of_eventually_nonzero
    (fun n => F n (x n)) (f z) hK hcompact u hu
  have hu₀ : u₀ ≠ 0 := by
    intro he
    rw [he,norm_zero] at hnorm
    norm_num at hnorm
  obtain ⟨L,_hLnorm,hLu⟩ := exists_dual_vector ℂ u₀ (by rw [hnorm]; norm_num)
  have hL₀ : L u₀=1 := by simpa [hnorm] using hLu
  obtain ⟨c,hc,hbase⟩ := compact_simple_kernel_estimate (f z) hcompact u₀ L
    (by rw [hL₀]; norm_num) (hker u₀ hu₀ hfix)
  have heK : ∀ᶠ n in atTop, ‖F n (x n)-f z‖ ≤ c/2 :=
    ((tendsto_iff_norm_sub_tendsto_zero.mp hK).eventually
      (gt_mem_nhds (half_pos hc))).mono (fun _ h => h.le)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (heK.and (hu.and hv))
  let k := fun n => n+N
  have hk : Tendsto k atTop atTop := tendsto_add_atTop_nat N
  have hg (n : ℕ) := hN (n+N) (Nat.le_add_left N n)
  have hLn (n : ℕ) : L (u (k n)) ≠ 0 :=
    spectral_kernel_functional_ne_zero (f z) _ L c hc hbase (hg n).1 _
      (hg n).2.1.1 (hg n).2.1.2
  let a := fun n => (L (u (k n)))⁻¹ • u (k n)
  let b := fun n => (L (u (k n)))⁻¹ • v (k n)
  have ha (n : ℕ) : F (k n) (x (k n)) (a n)=a n ∧ L (a n)=1 :=
    spectral_normalize_kernel _ L _ (hg n).2.1.1 (hLn n)
  have halim : Tendsto a atTop (𝓝 u₀) :=
    spectral_normalized_kernel_tendsto (fun n => F (k n) (x (k n))) (f z)
      (hK.comp hk) L c hc hbase (fun n => (hg n).1) u₀ a hfix
      (fun n => (ha n).1) (fun n => (ha n).2.trans hL₀.symm)
  have hb (n : ℕ) : b n-F (k n) (x (k n)) (b n)=deriv (F (k n)) (x (k n)) (a n) := by
    dsimp only [a,b]
    rw [map_smul,map_smul,← smul_sub,(hg n).2.2]
  exact compact_pencil_no_jordan_sequence (fun n => F (k n) (x (k n)))
    (fun n => deriv (F (k n)) (x (k n))) (f z) (deriv f z)
    (hK.comp hk) hcompact (hD.comp hk) L c hc hbase (fun n => (hg n).1)
    a b u₀ halim (fun n => (ha n).1) (fun n => (ha n).2) hb (hno u₀ hu₀ hfix)

end DefocusingNLS

end OAI
