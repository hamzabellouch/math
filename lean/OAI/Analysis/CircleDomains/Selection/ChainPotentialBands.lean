import OAI.Analysis.CircleDomains.Modulus.ChainPotentialOscillation
import OAI.Analysis.CircleDomains.Topology.ShrinkingJumpNeighborhoods

namespace OAI

/-! The topological band of the actual chain potential is controlled by
the dust toll at its center, once the shrinking jump levels are installed. -/

open Set Filter Metric
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem chainPotential_cluster_bound
    (R : X → X → ℝ≥0∞ → Prop) (hR : ∀ x y a, R x y a → R y x a)
    (E G : Set X) {m : X → ℝ≥0∞} (hm : (∑' x, m x ^ 2) ≠ ∞)
    {s : X} {V : ℕ → Set X} (hV : ∀ j, V j ∈ 𝓝 s)
    {r τ : ℕ → ℝ} (hVr : ∀ j, V j ⊆ ball s (r j))
    (hr : Tendsto r atTop (𝓝 0)) (hτ : Tendsto τ atTop (𝓝 0))
    {ρ : ℕ → ℝ≥0∞} (hρ : Tendsto ρ atTop (𝓝 0))
    (hj : ∀ j, ∀ x ∈ G ∩ V j, ∀ y ∈ G ∩ V j,
      R x y (max (ρ j) (neighborhoodTollSup m (thickening (τ j) (V j)))))
    {a b : ℝ} (ha : (s, a) ∈ clusterGraph G (realChainPotential R E))
    (hb : (s, b) ∈ clusterGraph G (realChainPotential R E)) :
    ENNReal.ofReal |a - b| ≤ 4 * m s :=
  (clusterGraph_oscillation_of_jumps R hR E G hV _ hj ha hb).trans
    (mul_le_mul' le_rfl (shrinking_thickening_toll_limsup hm hVr hr hτ hρ))

theorem chainPotential_boundary_band
    (R : X → X → ℝ≥0∞ → Prop) (hR : ∀ x y a, R x y a → R y x a)
    (E G : Set X) {m : X → ℝ≥0∞} (hm : (∑' x, m x ^ 2) ≠ ∞)
    {s : X} (hs : s ∈ closure G) {V : ℕ → Set X} (hV : ∀ j, V j ∈ 𝓝 s)
    {r τ : ℕ → ℝ} (hVr : ∀ j, V j ⊆ ball s (r j))
    (hr : Tendsto r atTop (𝓝 0)) (hτ : Tendsto τ atTop (𝓝 0))
    {ρ : ℕ → ℝ≥0∞} (hρ : Tendsto ρ atTop (𝓝 0))
    (hj : ∀ j, ∀ x ∈ G ∩ V j, ∀ y ∈ G ∩ V j,
      R x y (max (ρ j) (neighborhoodTollSup m (thickening (τ j) (V j))))) :
    ENNReal.ofReal (limsup (realChainPotential R E) (𝓝[G] s) -
      liminf (realChainPotential R E) (𝓝[G] s)) ≤ 4 * m s := by
  let : NeBot (𝓝[G] s) := mem_closure_iff_nhdsWithin_neBot.mp hs
  have he : ∀ᶠ x in 𝓝[G] s, 0 ≤ realChainPotential R E x ∧ realChainPotential R E x ≤ 1 :=
    Eventually.of_forall (realChainPotential_mem_Icc R E)
  have hlo := isBoundedUnder_of_eventually_ge (he.mono fun _ h => h.1)
  have hhi := isBoundedUnder_of_eventually_le (he.mono fun _ h => h.2)
  have ha : (s, limsup (realChainPotential R E) (𝓝[G] s)) ∈
      clusterGraph G (realChainPotential R E) :=
    mem_clusterGraph_iff_mapClusterPt.mpr
      (isGreatest_mapClusterPt_limsup hlo.isCoboundedUnder_le hhi).1
  have hb : (s, liminf (realChainPotential R E) (𝓝[G] s)) ∈
      clusterGraph G (realChainPotential R E) :=
    mem_clusterGraph_iff_mapClusterPt.mpr
      (isLeast_mapClusterPt_liminf hhi.isCoboundedUnder_ge hlo).1
  exact (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans
    (chainPotential_cluster_bound R hR E G hm hV hVr hr hτ hρ hj ha hb)

end CircleDomainRigidity

end

end OAI
