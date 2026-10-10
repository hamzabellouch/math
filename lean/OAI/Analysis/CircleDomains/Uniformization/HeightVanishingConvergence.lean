import OAI.Analysis.CircleDomains.Sobolev.HeightZeroEnergyLimit
import OAI.Analysis.CircleDomains.Modulus.HeightNormalization
import OAI.Analysis.CircleDomains.Topology.HeightCompactness

namespace OAI

/-! Compactness and uniqueness turn the energy tending to zero into
locally uniform convergence to the vertical coordinate. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem heights_tendsto_vertical_of_energy
    (v : ℕ → C(ℂ, ℝ)) (G₀ G₁ : ℕ → Lp ℝ 2 (volume : Measure EuclideanPlane))
    (hw : ∀ n, DeGiorgi.HasWeakGrad (heightLimitGradient (G₀ n) (G₁ n))
      (v n ∘ complexPlaneCoordinates) univ)
    (heq : Equicontinuous (fun n z => v n z))
    (hb : ∀ K : Set ℂ, IsCompact K → ∃ C : ℝ, ∀ n z, z ∈ K → |v n z| ≤ C)
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hE : ∀ n, (∫ p, G₀ n p^2+G₁ n p^2) ≤ e n)
    {R A : ℝ} (hd : ∀ n z, R ≤ ‖z‖ → |v n z-z.im| ≤ A/‖z‖) :
    TendstoLocallyUniformly (fun n z => v n z) Complex.im atTop := by
  let Y : C(ℂ, ℝ) := ⟨Complex.im, Complex.continuous_im⟩
  have ht : Tendsto v atTop (𝓝 Y) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨V, s, hs, hv⟩ := locally_uniform_height_subsequence (v ∘ ns) (heq.comp ns)
      (fun z => by
        obtain ⟨C, hC⟩ := hb {z} isCompact_singleton
        exact ⟨C, fun n => hC (ns n) z (mem_singleton z)⟩)
    have hwV := height_zero_energy_limit (fun n => v (ns (s n)))
      (fun n => G₀ (ns (s n))) (fun n => G₁ (ns (s n)))
      (fun n => hw (ns (s n))) hv
      (fun K hK => by
        obtain ⟨C, hC⟩ := hb K hK
        exact ⟨C, fun n => hC (ns (s n))⟩)
      (he.comp (hns.comp hs.tendsto_atTop)) (fun n => hE (ns (s n)))
    have hdV : ∀ z : ℂ, R ≤ ‖z‖ → |V z-z.im| ≤ A/‖z‖ := by
      intro z hz
      apply le_of_tendsto ((hv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)).sub_const z.im).abs
      exact Eventually.of_forall (fun n => hd (ns (s n)) z hz)
    have hV : V = Y := ContinuousMap.ext (congrFun
      (normalized_vertical_weak_gradient V.continuous hwV hdV))
    refine ⟨s, ?_⟩
    rw [hV] at hv
    exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr hv
  exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp ht

end CircleDomainRigidity

end

end OAI
