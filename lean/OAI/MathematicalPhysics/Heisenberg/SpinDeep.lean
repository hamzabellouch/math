import OAI.MathematicalPhysics.Heisenberg.SpinExhaustion

namespace OAI

section
noncomputable section
open scoped Classical
open Filter Topology
namespace Heisenberg

lemma dynamics_exhausting_locallyUniform (d ℓ : ℕ) (Γ : ℕ → Finset (Site d))
    (hΓ : ∀ F : Finset (Site d),∀ᶠ n : ℕ in atTop,F⊆Γ n) (A : QuasiLocal d ℓ) :
    TendstoLocallyUniformly (fun n t=>finiteDynamics d ℓ (Γ n) t A)
      (fun t=>dynamics d ℓ t A) atTop := by
  apply EquicontinuousLimits.locallyUniform
  · intro t
    exact (finiteDynamics_equicontinuous d ℓ A t).comp Γ
  · intro t
    exact dynamics_tendsto_exhausting d ℓ Γ hΓ t A

theorem finiteDynamics_deep_uniform (d ℓ : ℕ) (A : QuasiLocal d ℓ)
    (K : Set ℝ) (hK : IsCompact K) {ε : ℝ} (hε : 0<ε) :
    ∃ r : ℕ,∀ Γ : Finset (Site d),box d r⊆Γ →
      ∀ t∈K,dist (finiteDynamics d ℓ Γ t A) (dynamics d ℓ t A)<ε := by
  by_contra! hn
  choose Γ hΓ t ht he using hn
  have hex : ∀ F : Finset (Site d),∀ᶠ n : ℕ in atTop,F⊆Γ n := by
    intro F
    filter_upwards [eventually_subset_box F] with n hn
    exact hn.trans (hΓ n)
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    ((dynamics_exhausting_locallyUniform d ℓ Γ hex A).tendstoLocallyUniformlyOn)
  have hh := (Metric.tendstoUniformlyOn_iff.mp hu) ε hε
  obtain ⟨n,hn⟩:=hh.exists
  have hh':=hn (t n) (ht n)
  rw [dist_comm] at hh'
  exact (not_lt_of_ge (he n)) hh'

end Heisenberg
end
end

end OAI
