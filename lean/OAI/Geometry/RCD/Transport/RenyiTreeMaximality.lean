import OAI.Geometry.RCD.Transport.RenyiTreeCompression

namespace OAI

/-! # Variational properties of the compact maximal midpoint tree -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X] [CompleteSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem FollowsRenyiTree.maximal {n : ℕ} {K q : ℝ}
    {S : ∀ a : RenyiTransportNode n X, RenyiNodeSplit K q a} {m : ℕ} :
    ∀ {a : RenyiTransportNode n X} {ν : Time → Measure X}, FollowsRenyiTree S a ν m →
      RenyiDyadicMaximal (hausdorff n X) q ν m := by
  induction m with
  | zero => intro a ν h; trivial
  | succ m ih =>
    intro a ν h
    refine ⟨?_,ih h.2.2.2.1,ih h.2.2.2.2⟩
    intro κ hκ hgκ hpκ
    rw [h.1,h.2.1] at hpκ
    rw [h.2.2.1]
    exact (S a).maximal κ hκ hgκ hpκ

omit [SeparableSpace X] in
theorem NoncollapsedRCD.exists_compressed_maximal_renyi_tree
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (a : RenyiTransportNode n X) :
    ∃ π : Measure C(Time,X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧ IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))) ∧
      (∀ t : Time, π.map (fun γ => γ t) ≤ compressionBudget K n a.distance a.capacity • hausdorff n X) ∧
      ∀ m, RenyiDyadicMaximal (hausdorff n X) q (fun t => π.map (fun γ => γ t)) m := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let S := hX.selectedRenyiSplit K n hn q hq0 hq1
  obtain ⟨π,hπ,hg,hp,hf⟩ := exists_plan_following_all_renyi_levels S a
  let := hπ
  exact ⟨π,hπ,hg,hp,hX.plan_following_renyi_tree_compression K n hn S a π hg hp hf,
    fun m => (hf m).maximal⟩

end RegularPointCoordinates

end

end OAI
