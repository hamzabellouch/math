import Mathlib
import OAI.Probability.CriticalPercolation.Modular.ClusterTransportGeometry

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*} (G : BondGraph V E)

def weight (r s : ℕ) (ω : Set E) (v : V) : ℝ :=
  if small G r ω v then mass G s ω v else 0

def transport (r s : ℕ) (p : ℝ) (ω : Set E) (v : V) (e : E) : ℝ :=
  if e ∈ G.incidentEdges (G.cluster ω v) then weight G r s ω v * coefficient p ω e else 0

def clusterWeight (r s : ℕ) (ω : Set E) (v : V) : ℝ :=
  if small G r ω v then cappedMass s (size G ω v) else 0

def truncatedEdgeMass (r s : ℕ) (ω : Set E) (e : E) : ℝ :=
  clusterWeight G r s ω (G.ends e).out.1 +
    if (G.openGraph ω).Reachable (G.ends e).out.1 (G.ends e).out.2 then 0
    else clusterWeight G r s ω (G.ends e).out.2

lemma weight_reachable (r s : ℕ) {ω : Set E} {u v : V}
    (h : (G.openGraph ω).Reachable u v) : weight G r s ω u = weight G r s ω v := by
  rw [weight,weight,small_reachable G r h,mass_eq_of_reachable G s h]

lemma weight_nonneg (r s : ℕ) (ω : Set E) (v : V) : 0 ≤ weight G r s ω v := by
  unfold weight
  split_ifs
  · exact mass_nonneg G s ω v
  · rfl

lemma clusterWeight_nonneg (r s : ℕ) (ω : Set E) (v : V) : 0 ≤ clusterWeight G r s ω v := by
  unfold clusterWeight
  split_ifs
  · exact cappedMass_nonneg _ _
  · rfl

lemma clusterWeight_le (r s : ℕ) (ω : Set E) (v : V) :
    clusterWeight G r s ω v ≤ cappedMass s (size G ω v) := by
  unfold clusterWeight
  split_ifs
  · rfl
  · exact cappedMass_nonneg _ _

lemma weighted_cluster_summable (hl : G.LocallyFinite) (r s : ℕ) (ω : Set E) (x : V) :
    Summable (fun u => if u ∈ G.cluster ω x then weight G r s ω u else 0) := by
  by_cases hs : small G r ω x
  · apply summable_of_ne_finset_zero (s := (small_finite G hl hs).toFinset)
    intro u hu
    simpa only [Set.Finite.mem_toFinset,not_false_eq_true] using
      (ite_eq_right (show u ∉ G.cluster ω x from fun h => hu ((small_finite G hl hs).mem_toFinset.mpr h)) :
        (if u ∈ G.cluster ω x then weight G r s ω u else 0) = 0)
  · have hz : (fun u => if u ∈ G.cluster ω x then weight G r s ω u else 0) = 0 := by
      funext u
      by_cases hu : u ∈ G.cluster ω x
      · rw [ite_eq_left hu,← weight_reachable G r s hu,weight,ite_eq_right hs]
        rfl
      · simp [hu]
    rw [hz]
    exact summable_zero

lemma tsum_weighted_cluster (hl : G.LocallyFinite) (r s : ℕ) (ω : Set E) (x : V) :
    (∑' u, if u ∈ G.cluster ω x then weight G r s ω u else 0) = clusterWeight G r s ω x := by
  by_cases hs : small G r ω x
  · have hC := small_finite G hl hs
    have hpos : 0 < size G ω x := (Set.ncard_pos hC).mpr ⟨x,SimpleGraph.Reachable.refl x⟩
    rw [tsum_eq_sum (s := hC.toFinset) (fun u hu => ite_eq_right (fun h => hu (hC.mem_toFinset.mpr h)))]
    calc
      _ = ∑ _u ∈ hC.toFinset, mass G s ω x := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [ite_eq_left (hC.mem_toFinset.mp hu),← weight_reachable G r s (hC.mem_toFinset.mp hu),weight,ite_eq_left hs]
      _ = _ := by
        rw [Finset.sum_const,nsmul_eq_mul,← Set.ncard_eq_toFinset_card _ hC]
        change (size G ω x : ℝ) * (cappedMass s (size G ω x) / size G ω x) = _
        rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hpos.ne')]
        exact (ite_eq_left hs).symm
  · rw [clusterWeight,ite_eq_right hs]
    calc
      _ = ∑' _u : V, (0:ℝ) := by
        apply tsum_congr
        intro u
        by_cases hu : u ∈ G.cluster ω x
        · rw [ite_eq_left hu,← weight_reachable G r s hu,weight,ite_eq_right hs]
        · rw [ite_eq_right hu]
      _ = 0 := tsum_zero

lemma transport_sum_out (r s : ℕ) (p : ℝ) (ω : Set E) (u : V) :
    (∑' e, transport G r s p ω u e) = if small G r ω u then rootDiscrepancy G s p ω u else 0 := by
  have hf : (fun e => transport G r s p ω u e) =
      (fun e => weight G r s ω u * (if e ∈ G.incidentEdges (G.cluster ω u) then coefficient p ω e else 0)) := by
    funext e
    unfold transport
    split_ifs <;> simp
  rw [hf,tsum_mul_left]
  unfold weight rootDiscrepancy rootSum
  split_ifs <;> simp

lemma transport_sum_in (hl : G.LocallyFinite) (r s : ℕ) (p : ℝ) (ω : Set E) (e : E) :
    (∑' u, transport G r s p ω u e) = coefficient p ω e * truncatedEdgeMass G r s ω e := by
  let x := (G.ends e).out.1
  let y := (G.ends e).out.2
  have hi (u : V) : e ∈ G.incidentEdges (G.cluster ω u) ↔
      u ∈ G.cluster ω x ∪ G.cluster ω y := by
    exact Set.ext_iff.mp (incidentRoots G ω e) u
  by_cases hxy : (G.openGraph ω).Reachable x y
  · have heq := G.cluster_eq_of_reachable hxy
    have hf : (fun u => transport G r s p ω u e) =
        fun u => coefficient p ω e * (if u ∈ G.cluster ω x then weight G r s ω u else 0) := by
      funext u
      unfold transport
      rw [hi,← heq,Set.union_self]
      split_ifs <;> ring
    rw [hf,tsum_mul_left,tsum_weighted_cluster G hl]
    simp only [truncatedEdgeMass,show (G.openGraph ω).Reachable (G.ends e).out.1 (G.ends e).out.2 from hxy,ite_true,add_zero]
    rfl
  · have hd := G.cluster_disjoint_of_not_reachable hxy
    have hf : (fun u => transport G r s p ω u e) = fun u => coefficient p ω e *
        ((if u ∈ G.cluster ω x then weight G r s ω u else 0) +
          (if u ∈ G.cluster ω y then weight G r s ω u else 0)) := by
      funext u
      unfold transport
      rw [hi]
      by_cases hx : u ∈ G.cluster ω x
      · have hy : u ∉ G.cluster ω y := fun hy => Set.disjoint_left.mp hd hx hy
        simp only [hx,hy,Set.mem_union,true_or,ite_true,ite_false,add_zero]
        ring
      · by_cases hy : u ∈ G.cluster ω y
        · simp only [hx,hy,Set.mem_union,or_true,ite_true,ite_false,zero_add]; ring
        · simp only [hx,hy,Set.mem_union,or_false,ite_false,add_zero,mul_zero]
    rw [hf,tsum_mul_left,(weighted_cluster_summable G hl r s ω x).tsum_add
      (weighted_cluster_summable G hl r s ω y),tsum_weighted_cluster G hl,tsum_weighted_cluster G hl]
    simp only [truncatedEdgeMass,show ¬(G.openGraph ω).Reachable (G.ends e).out.1 (G.ends e).out.2 from hxy,ite_false]
    rfl

lemma truncatedEdgeMass_nonneg (r s : ℕ) (ω : Set E) (e : E) :
    0 ≤ truncatedEdgeMass G r s ω e := by
  unfold truncatedEdgeMass
  split_ifs
  · simpa using clusterWeight_nonneg G r s ω (G.ends e).out.1
  · exact add_nonneg (clusterWeight_nonneg G r s ω _) (clusterWeight_nonneg G r s ω _)

lemma truncatedEdgeMass_le (r s : ℕ) (ω : Set E) (e : E) :
    truncatedEdgeMass G r s ω e ≤ edgeMass G s ω e := by
  unfold truncatedEdgeMass edgeMass
  split_ifs
  · simpa using clusterWeight_le G r s ω (G.ends e).out.1
  · exact add_le_add (clusterWeight_le G r s ω _) (clusterWeight_le G r s ω _)

lemma transport_sum_in_bound (hl : G.LocallyFinite) (r s : ℕ) {p : ℝ}
    (hp : p ∈ Ioo 0 1) (ω : Set E) (e : E) :
    |∑' u, transport G r s p ω u e| ≤ 2/p := by
  rw [transport_sum_in G hl,abs_mul,abs_of_nonneg (truncatedEdgeMass_nonneg G r s ω e)]
  calc
    _ ≤ (1/p)*2 := mul_le_mul (coefficient_abs_le hp ω e)
      ((truncatedEdgeMass_le G r s ω e).trans (edgeMass_le_two G s ω e))
      (truncatedEdgeMass_nonneg G r s ω e) (div_nonneg zero_le_one hp.1.le)
    _ = _ := by ring

end CriticalPercolation.FiniteClusters
end
end

end OAI
