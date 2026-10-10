import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHolomorphicDifference

namespace OAI

/-! Joint limits at every spectral parameter give locally uniform convergence. -/

open Set Filter Topology
namespace DefocusingNLS
variable {E : Type*} [NormedAddCommGroup E]

theorem spectral_locallyUniform_of_joint
    (F : ℕ → ℂ → E) (f : ℂ → E) (U : Set ℂ) (hU : IsOpen U)
    (hf : ContinuousOn f U)
    (h : ∀ z ∈ U, Tendsto (fun p : ℕ × ℂ => F p.1 p.2)
      (atTop ×ˢ 𝓝 z) (𝓝 (f z))) :
    TendstoLocallyUniformlyOn F f atTop U := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε z hz
  have he := Metric.tendsto_nhds.mp (h z hz) (ε/2) (half_pos hε)
  obtain ⟨A,hA,B,hB,hAB⟩ := Filter.mem_prod_iff.mp he
  have hc : {w : ℂ | dist (f w) (f z) < ε/2} ∈ 𝓝 z :=
    (hf.continuousAt (hU.mem_nhds hz)).tendsto.eventually
      (Metric.ball_mem_nhds (f z) (half_pos hε))
  refine ⟨B ∩ {w : ℂ | dist (f w) (f z) < ε/2},
    mem_nhdsWithin_of_mem_nhds (inter_mem hB hc), ?_⟩
  filter_upwards [hA] with n hn w hw
  have hew : dist (F n w) (f z) < ε/2 := hAB (show (n,w) ∈ A ×ˢ B from ⟨hn,hw.1⟩)
  calc
    dist (f w) (F n w) ≤ dist (f w) (f z)+dist (f z) (F n w) := dist_triangle _ _ _
    _ < ε/2+ε/2 := add_lt_add hw.2 (by simpa only [dist_comm] using hew)
    _ = ε := add_halves ε

end DefocusingNLS

end OAI
