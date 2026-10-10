import OAI.Probability.SLE.Loewner.LoewnerKernelContinuity

namespace OAI

/-! Compact subsets of the limiting surviving domain stay in the
surviving domains of all sufficiently close drivers. -/
noncomputable section
open Set Filter
open scoped Topology NNReal

namespace SLEExactGauge

theorem compact_survival_of_inverse_convergence
    (U : ℕ → ℝ≥0 → ℝ) (γ : ℕ → ℝ≥0 → ℂ) (G F : ℕ → ℝ≥0 → ℂ → ℂ)
    (h : ∀ n, IsCapacityTwoWitness (U n) (γ n) (G n) (F n))
    {V : ℝ≥0 → ℝ} {β : ℝ≥0 → ℂ} {H J : ℝ≥0 → ℂ → ℂ}
    (hv : IsCapacityTwoWitness V β H J) (T : ℝ≥0)
    (hl : TendstoLocallyUniformlyOn (fun n => F n T) (J T) atTop upperHalfPlane)
    {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ survivingDomain β T) :
    ∀ᶠ n in atTop, K ⊆ survivingDomain (γ n) T := by
  classical
  have hp (z : K) : ∃ r : ℝ, 0 < r ∧
      ∀ᶠ n in atTop, Metric.ball (z:ℂ) r ⊆ survivingDomain (γ n) T := by
    obtain ⟨r,hr,he⟩ := inverse_image_neighborhood_persists U γ G F h hv T hl
      (hv.2.2.2.2.2.1 T (hKD z.property))
    rw [hv.2.2.2.2.2.2.2.1 T z (hKD z.property)] at he
    exact ⟨r,hr,he⟩
  choose r hr hp using hp
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun z : K => Metric.ball (z:ℂ) (r z))
    (fun _ => Metric.isOpen_ball) (fun z hz =>
      mem_iUnion.mpr ⟨⟨z,hz⟩,Metric.mem_ball_self (hr ⟨z,hz⟩)⟩)
  have he : ∀ᶠ n in atTop, ∀ z ∈ s, Metric.ball (z:ℂ) (r z) ⊆ survivingDomain (γ n) T := by
    exact s.eventually_all.mpr (fun z _ => hp z)
  filter_upwards [he] with n hn z hz
  obtain ⟨w,hw,hwz⟩ := mem_iUnion₂.mp (hs hz)
  exact hn w hw hwz

end SLEExactGauge

end

end OAI
