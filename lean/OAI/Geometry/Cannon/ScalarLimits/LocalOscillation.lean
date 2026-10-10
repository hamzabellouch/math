import Mathlib
import OAI.Geometry.Cannon.Modulus.Cost
import OAI.Geometry.Cannon.PlaneTopology.Hat
import OAI.Geometry.Cannon.Energy.LiftPath

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Metric Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval

namespace CannonScalarLocal

open CannonGrid CannonCells CannonRegularization CannonChart

variable {X ι : Type*} [MetricSpace X] [Fintype ι]

local instance : LocallyPathConnectedSpace unitInterval :=
  (isQuotientMap_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).locallyPathConnectedSpace

local instance : PathConnectedSpace Square :=
  pathConnectedSpace_iff_connectedSpace.mpr inferInstance

theorem local_oscillation
    (e : Square → X) (he : Topology.IsEmbedding e)
    (L J r : ℝ) (hL : 1 ≤ L) (hJ : 0 < J) (hr : 0 < r)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < L*s} u v)
    (x : X) (hchart : Metric.ball x (L*(L*J+1)*r) ⊆ range e)
    (q : ι → X) (ρ : ι → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (raw : Square → ℝ) (hrawI : ∀ z, raw z ∈ Icc 0 1)
    (hraw : ∀ a b : Square, ∀ p : Path a b,
      |raw a-raw b| ≤ cost (fun i => e ⁻¹' Metric.ball (q i) (2*r)) ρ (range p))
    (N : ℕ) (hN : 0 < N)
    (hmesh : ∀ z : Square, ∀ i : Index N, weight N z i ≠ 0 →
      dist (e z) (e (vertex N hN i)) < r)
    (T B : Set Square) (hT : T.Nonempty) (hB : B.Nonempty)
    (a b : Square) (ha : dist x (e a) ≤ J*r) (hb : dist x (e b) ≤ J*r) :
    |drain (flood (interpolate N hN raw) T) B a -
      drain (flood (interpolate N hN raw) T) B b| ≤
      ∑ i ∈ Finset.univ.filter (fun i => dist (q i) x ≤ (L*(L*J+1)+3)*r), ρ i := by
  classical
  have hLp : 0 < L := by linarith
  have hinner : 0 < L*J+1 := by positivity
  have hrad : L*(J*r) ≤ L*(L*J+1)*r := by
    have hj : J ≤ L*J := le_mul_of_one_le_left hJ.le hL
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (show J ≤ L*J+1 by linarith) hLp.le) hr.le
    simpa only [mul_assoc] using hh
  have hsmall : {z : X | dist x z < L*(J*r)} ⊆ range e := by
    intro z hz
    apply hchart
    rw [Metric.mem_ball,dist_comm]
    exact hz.trans_le hrad
  obtain ⟨p,hp⟩ := lift_joinedIn e he hsmall (hpaths x (e a) (e b) (J*r)
    (mul_pos hJ hr) ha hb)
  apply flood_drain_path_osc (continuous_interpolate N hN raw) hT hB
    (fun z => interpolate_bounds N hN raw hrawI z) p
  intro s t
  apply interpolate_variation
  intro i j hi hj
  have hvi : dist x (e (vertex N hN i)) ≤ (L*J+1)*r := by
    have hd := dist_triangle x (e (p s)) (e (vertex N hN i))
    have hh := hp s
    change dist x (e (p s)) < L*(J*r) at hh
    have hm := hmesh (p s) i hi
    nlinarith
  have hvj : dist x (e (vertex N hN j)) ≤ (L*J+1)*r := by
    have hd := dist_triangle x (e (p t)) (e (vertex N hN j))
    have hh := hp t
    change dist x (e (p t)) < L*(J*r) at hh
    have hm := hmesh (p t) j hj
    nlinarith
  have hlarge : {z : X | dist x z < L*((L*J+1)*r)} ⊆ range e := by
    intro z hz
    apply hchart
    simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_comm,mul_assoc] using hz
  obtain ⟨p',hp'⟩ := lift_joinedIn e he hlarge
    (hpaths x _ _ ((L*J+1)*r) (mul_pos hinner hr) hvi hvj)
  apply (hraw _ _ p').trans
  unfold cost
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    obtain ⟨z,⟨u,rfl⟩,hcell⟩ := (mem_indices _ _ k).mp hk
    have hh := hp' u
    change dist x (e (p' u)) < L*((L*J+1)*r) at hh
    change dist (e (p' u)) (q k) < 2*r at hcell
    have ht := dist_triangle (q k) (e (p' u)) x
    rw [dist_comm (q k) (e (p' u)),dist_comm (e (p' u)) x] at ht
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    nlinarith
  · intro k _ _
    exact hρ k

end CannonScalarLocal

end
end
end
end
end
end
end
end
end

end OAI
