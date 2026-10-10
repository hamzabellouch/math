import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevForwardDomain

namespace OAI

/-! # Uniform stability on compact intervals before blowup -/

open Filter Topology Set Metric

namespace DefocusingNLS

/-- On every compact interval before the reference solution's maximal time, one neighborhood
of its initial datum gives existence and uniform Sobolev closeness throughout that interval. -/
theorem maximalSobolevSchrodingerFlow_compact_stability
    (k : ℝ) (hk : 6 < k) (m : ℕ) (f : FourierL2) (T ε : ℝ) (hε : 0 < ε)
    (hdom : T ∈ maximalSobolevInteractionDomain k hk m f) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : FourierL2, dist g f < δ → ∀ t ∈ Icc 0 T,
      t ∈ maximalSobolevInteractionDomain k hk m g ∧
        dist (maximalSobolevSchrodingerFlow k hk m g t)
          (maximalSobolevSchrodingerFlow k hk m f t) < ε := by
  have hseg : Icc 0 T ⊆ maximalSobolevInteractionDomain k hk m f :=
    (isPreconnected_maximalSobolevInteractionDomain k hk m f).Icc_subset
      (zero_mem_maximalSobolevInteractionDomain k hk m f) hdom
  have hevent : ∀ᶠ g : FourierL2 in 𝓝 f, ∀ t ∈ Icc 0 T,
      t ∈ maximalSobolevInteractionDomain k hk m g ∧
        dist (maximalSobolevSchrodingerFlow k hk m g t)
          (maximalSobolevSchrodingerFlow k hk m f t) < ε := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hf := hasSobolevFlowNeighborhood_of_nonneg k hk m f t ht.1 (hseg ht)
    have hc : ContinuousAt (maximalSobolevSchrodingerFlow k hk m f) t :=
      (continuousOn_maximalSobolevSchrodingerFlow k hk m f t (hseg ht)).continuousAt
        ((isOpen_maximalSobolevInteractionDomain k hk m f).mem_nhds (hseg ht))
    have href : ContinuousAt
        (fun p : FourierL2 × ℝ => maximalSobolevSchrodingerFlow k hk m f p.2) (f, t) :=
      ContinuousAt.comp (f := fun p : FourierL2 × ℝ => p.2)
        (g := maximalSobolevSchrodingerFlow k hk m f) hc continuous_snd.continuousAt
    have hd : ContinuousAt (fun p : FourierL2 × ℝ =>
        dist (maximalSobolevSchrodingerFlow k hk m p.1 p.2)
          (maximalSobolevSchrodingerFlow k hk m f p.2)) (f, t) := hf.2.dist href
    have he : ∀ᶠ p : FourierL2 × ℝ in 𝓝 (f, t),
        dist (maximalSobolevSchrodingerFlow k hk m p.1 p.2)
          (maximalSobolevSchrodingerFlow k hk m f p.2) < ε :=
      hd.tendsto.eventually (isOpen_Iio.mem_nhds (by simpa using hε))
    filter_upwards [hf.1, he] with p hp hd
    exact ⟨hp, hd⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hevent
  exact ⟨δ, hδ, fun g hg => hball hg⟩

/-- Reaching a specified open set at a fixed forward time is an open condition on the datum. -/
theorem isOpen_maximalSobolev_terminal_condition
    (k : ℝ) (hk : 6 < k) (m : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (V : Set FourierL2) (hV : IsOpen V) :
    IsOpen {f : FourierL2 | T ∈ maximalSobolevInteractionDomain k hk m f ∧
      maximalSobolevSchrodingerFlow k hk m f T ∈ V} := by
  apply isOpen_iff_mem_nhds.mpr
  intro f hf
  have hflow := hasSobolevFlowNeighborhood_of_nonneg k hk m f T hT hf.1
  have hp : ContinuousAt (fun g : FourierL2 => (g, T)) f :=
    (continuous_id.prodMk continuous_const).continuousAt
  have hc : ContinuousAt (fun g : FourierL2 => maximalSobolevSchrodingerFlow k hk m g T) f :=
    ContinuousAt.comp (f := fun g : FourierL2 => (g, T))
      (g := fun p : FourierL2 × ℝ => maximalSobolevSchrodingerFlow k hk m p.1 p.2)
      hflow.2 hp
  have hdom : ∀ᶠ g : FourierL2 in 𝓝 f,
      T ∈ maximalSobolevInteractionDomain k hk m g := hp.tendsto.eventually hflow.1
  exact hdom.and (hc.tendsto.eventually (hV.mem_nhds hf.2))

end DefocusingNLS

end OAI
