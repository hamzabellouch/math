import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M]
include I

lemma riemannian_approximate_midpoint (x y : M) {eps : ℝ} (heps : 0 < eps) :
    ∃ z : M, dist x z = dist x y/2 ∧ dist z y < dist x y/2+eps := by
  have hdist : riemannianEDist I x y < ENNReal.ofReal (dist x y+eps) := by
    rw [← IsRiemannianManifold.out,edist_dist]
    exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr (by linarith)
  obtain ⟨γ,hγ0,hγ1,hγ,hlen⟩ := exists_lt_of_riemannianEDist_lt hdist
  have hc : ContinuousOn (fun t : ℝ => dist x (γ t)) (Icc 0 1) :=
    continuous_dist.comp_continuousOn (continuousOn_const.prodMk hγ.continuousOn)
  have hhalf : dist x y/2 ∈ Icc (dist x (γ 0)) (dist x (γ 1)) := by
    rw [hγ0,hγ1,dist_self]
    constructor <;> linarith [dist_nonneg (x := x) (y := y)]
  obtain ⟨t,ht,htt⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hc hhalf
  change dist x (γ t) = dist x y/2 at htt
  refine ⟨γ t,htt,?_⟩
  have hpre := riemannianEDist_le_pathELength (I := I)
    (hγ.mono (Icc_subset_Icc le_rfl ht.2)) hγ0 rfl ht.1
  have hpost := riemannianEDist_le_pathELength (I := I)
    (hγ.mono (Icc_subset_Icc ht.1 le_rfl)) rfl hγ1 ht.2
  have hsum : ENNReal.ofReal (dist x (γ t)+dist (γ t) y) <
      ENNReal.ofReal (dist x y+eps) := by
    rw [ENNReal.ofReal_add dist_nonneg dist_nonneg]
    rw [← IsRiemannianManifold.out,edist_dist] at hpre hpost
    exact (add_le_add hpre hpost).trans_lt ((pathELength_add ht.1 ht.2).trans_lt hlen)
  have hsumR : dist x (γ t)+dist (γ t) y < dist x y+eps :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hsum
  rw [htt] at hsumR
  linarith

lemma riemannian_exists_midpoint [CompactSpace M] (x y : M) :
    ∃ z : M, dist x z = dist x y/2 ∧ dist z y = dist x y/2 := by
  let F : M → ℝ := fun z => max (dist x z) (dist z y)
  have hc : Continuous F := by fun_prop
  obtain ⟨z,_,hz⟩ := isCompact_univ.exists_isMinOn ⟨x,mem_univ x⟩ hc.continuousOn
  have hF : F z ≤ dist x y/2 := by
    by_contra hn
    have hp : 0 < F z-dist x y/2 := sub_pos.mpr (lt_of_not_ge hn)
    obtain ⟨w,hwx,hwy⟩ := riemannian_approximate_midpoint (I := I) x y (half_pos hp)
    have hw : F w < F z := by
      dsimp [F]
      apply max_lt
      · rw [hwx]; linarith
      · linarith
    exact (not_lt_of_ge (hz (mem_univ w))) hw
  have hx := (le_max_left (dist x z) (dist z y)).trans hF
  have hy := (le_max_right (dist x z) (dist z y)).trans hF
  have htri := dist_triangle x z y
  exact ⟨z,by linarith,by linarith⟩

end WeakMTWTransport

end

end OAI
