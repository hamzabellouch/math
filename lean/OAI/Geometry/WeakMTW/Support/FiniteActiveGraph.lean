import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.HopfRinow
import OAI.Geometry.WeakMTW.Coordinates.TangentDiskCompact

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]
  {ι : Type*} [Fintype ι] [Nonempty ι]

 def finitePotential (y : ι → M) (h : ι → ℝ) (x : M) : ℝ :=
    Finset.univ.sup' Finset.univ_nonempty (fun i => h i - cost x (y i))

 def activeVelocities (y : ι → M) (h : ι → ℝ) (x : M) : Set (TangentSpace (model n) x) :=
    {a | a ∈ minimizingDomain x ∧ ∃ i, exp x a = y i ∧ finitePotential y h x = h i-cost x (y i)}

 def activeHull (y : ι → M) (h : ι → ℝ) (x : M) : Set (TangentSpace (model n) x) :=
    convexHull ℝ (activeVelocities y h x)

 def activeGraph (y : ι → M) (h : ι → ℝ) : Set (TangentBundle (model n) M) :=
    {p | p.2 ∈ activeVelocities y h p.1}

 def activeHullGraph (y : ι → M) (h : ι → ℝ) : Set (TangentBundle (model n) M) :=
    {p | p.2 ∈ activeHull y h p.1}

omit [CompactSpace M] in
 theorem cost_continuous : Continuous (fun p : M × M => cost p.1 p.2) :=
    (continuous_fst.dist continuous_snd |>.pow 2).div_const 2

omit [CompactSpace M] in
 theorem finitePotential_continuous (y : ι → M) (h : ι → ℝ) : Continuous (finitePotential y h) := by
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro i _
  exact continuous_const.sub ((continuous_id.dist continuous_const).pow 2 |>.div_const 2)

omit [CompactSpace M] in
 theorem finitePotential_ge (y : ι → M) (h : ι → ℝ) (x : M) (i : ι) :
    h i-cost x (y i) ≤ finitePotential y h x :=
    Finset.le_sup' (fun j => h j-cost x (y j)) (Finset.mem_univ i)

omit [CompactSpace M] in
 theorem finitePotential_attained (y : ι → M) (h : ι → ℝ) (x : M) :
    ∃ i, finitePotential y h x = h i-cost x (y i) := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => h i-cost x (y i))
  exact ⟨i,hi⟩

 theorem activeVelocities_nonempty (y : ι → M) (h : ι → ℝ) (x : M) :
    (activeVelocities (n := n) y h x).Nonempty := by
  obtain ⟨i,hi⟩ := finitePotential_attained y h x
  obtain ⟨a,ha,han⟩ := exists_minimizing_vector (n := n) x (y i)
  refine ⟨a,?_,i,ha,hi⟩
  change dist x (exp x a) = ‖a‖
  rw [ha,han]

omit [IsManifold (model n) ∞ M]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem activeGraph_eq (y : ι → M) (h : ι → ℝ) :
    activeGraph y h = ⋃ i : ι, totalMinimizingSet (n := n) (M := M) ∩
      {p : TangentBundle (model n) M | exp p.1 p.2 = y i ∧ finitePotential y h p.1 = h i-cost p.1 (y i)} := by
  ext p
  simp only [activeGraph,activeVelocities,mem_ofPred_eq,mem_iUnion,mem_inter_iff]
  exact ⟨fun ⟨hp,i,hi⟩ => ⟨i,hp,hi⟩,fun ⟨i,hp,hi⟩ => ⟨hp,i,hi⟩⟩

 theorem activeGraph_compact (y : ι → M) (h : ι → ℝ) : IsCompact (activeGraph (n := n) y h) := by
  rw [activeGraph_eq]
  apply isCompact_iUnion
  intro i
  apply totalMinimizingSet_compact.inter_right
  apply IsClosed.inter
  · exact isClosed_eq exp_total_smooth.continuous continuous_const
  · have hb : Continuous (fun p : TangentBundle (model n) M => p.1) :=
      (contMDiff_proj (TangentSpace (model n)) (IB := model n) (n := ∞)).continuous
    exact isClosed_eq ((finitePotential_continuous y h).comp hb)
      (continuous_const.sub ((hb.dist continuous_const).pow 2 |>.div_const 2))

omit [IsManifold (model n) ∞ M]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] in
 theorem activeHull_bound (y : ι → M) (h : ι → ℝ) (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ activeHull y h x) : ‖v‖ ≤ Metric.diam (univ : Set M) := by
  have hsub : activeVelocities (n := n) y h x ⊆ Metric.closedBall 0 (Metric.diam (univ : Set M)) := by
    intro a ha
    rw [Metric.mem_closedBall,dist_zero_right,← show dist x (exp x a) = ‖a‖ from ha.1]
    exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)
  have hmem := convexHull_min hsub (convex_closedBall (0 : TangentSpace (model n) x) _) hv
  simpa only [Metric.mem_closedBall,dist_zero_right] using hmem

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
