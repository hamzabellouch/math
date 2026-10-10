import Mathlib

namespace OAI

section
section
section
noncomputable section
namespace CannonTangentSegments
open Set Metric

theorem no_triple_closedBalls {u v w x : ℂ} {a b c : ℝ}
    (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (huv : a+b≤dist u v) (huw : a+c≤dist u w) (hvw : b+c≤dist v w)
    (hxu : dist u x≤a) (hxv : dist v x≤b) (hxw : dist w x≤c) : False := by
  have hvu:=dist_triangle u x v
  have hwu:=dist_triangle u x w
  have hwv:=dist_triangle v x w
  rw [dist_comm x v] at hvu
  rw [dist_comm x w] at hwu hwv
  have exu : dist u x=a := by linarith
  have exv : dist v x=b := by linarith
  have exw : dist w x=c := by linarith
  have Huv : x∈segment ℝ u v := mem_segment_iff_wbtw.mpr
    (dist_add_dist_eq_iff.mp (by rw [dist_comm x v]; linarith))
  have Huw : x∈segment ℝ u w := mem_segment_iff_wbtw.mpr
    (dist_add_dist_eq_iff.mp (by rw [dist_comm x w]; linarith))
  have Hvw : x∈segment ℝ v w := mem_segment_iff_wbtw.mpr
    (dist_add_dist_eq_iff.mp (by rw [dist_comm x w]; linarith))
  have hxu0 : x-u≠0 := sub_ne_zero.mpr (by intro h; subst x; simp at exu; linarith)
  have hxw0 : w-x≠0 := sub_ne_zero.mpr (by intro h; subst w; simp at exw; linarith)
  have hxv0 : v-x≠0 := sub_ne_zero.mpr (by intro h; subst v; simp at exv; linarith)
  have hr := (sameRay_of_mem_segment Huv).symm.trans (sameRay_of_mem_segment Huw)
    (fun h=>(hxu0 h).elim)
  have hn := hr.trans (sameRay_of_mem_segment Hvw).symm (fun h=>(hxw0 h).elim)
  have hn' : SameRay ℝ (v-x) (-(v-x)) := by simpa only [neg_sub] using hn
  exact hxv0 (eq_zero_of_sameRay_self_neg hn')

theorem center_not_mem_edge {u v w : ℂ} {a b c : ℝ}
    (hc : 0<c) (huv : dist u v=a+b)
    (huw : a+c≤dist u w) (hvw : b+c≤dist v w) : w∉segment ℝ u v := by
  intro hw
  have H : dist u w+dist w v=dist u v := dist_add_dist_eq_iff.mpr (mem_segment_iff_wbtw.mp hw)
  rw [huv,dist_comm w v] at H
  linarith

theorem disjoint_edges {u v w z : ℂ} {a b c d : ℝ}
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d)
    (huv : dist u v=a+b) (hwz : dist w z=c+d)
    (huw : a+c≤dist u w) (huz : a+d≤dist u z)
    (hvw : b+c≤dist v w) (hvz : b+d≤dist v z) :
    Disjoint (segment ℝ u v) (segment ℝ w z) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have H : dist u x+dist x v=dist u v := dist_add_dist_eq_iff.mpr (mem_segment_iff_wbtw.mp hx)
  have K : dist w x+dist x z=dist w z := dist_add_dist_eq_iff.mpr (mem_segment_iff_wbtw.mp hy)
  rw [huv,dist_comm x v] at H
  rw [hwz,dist_comm x z] at K
  have het (p q s : ℂ) (r t : ℝ) (hp : dist p s≤r) (hq : dist q s≤t)
      (hpq : r+t≤dist p q) : dist p s=r := by
    have hh:=dist_triangle p s q
    rw [dist_comm s q] at hh
    linarith
  by_cases hxu : dist u x≤a
  · by_cases hxw : dist w x≤c
    · have exu:=het u w x a c hxu hxw huw
      have hxv : dist v x≤b := by linarith
      exact no_triple_closedBalls ha hb hc huv.ge huw hvw hxu hxv hxw
    · have hxz : dist z x≤d := by linarith
      have exu:=het u z x a d hxu hxz huz
      have hxv : dist v x≤b := by linarith
      exact no_triple_closedBalls ha hb hd huv.ge huz hvz hxu hxv hxz
  · have hxv : dist v x≤b := by linarith
    by_cases hxw : dist w x≤c
    · have exv:=het v w x b c hxv hxw hvw
      have hxu : dist u x≤a := by linarith
      exact no_triple_closedBalls ha hb hc huv.ge huw hvw hxu hxv hxw
    · have hxz : dist z x≤d := by linarith
      have exv:=het v z x b d hxv hxz hvz
      have hxu : dist u x≤a := by linarith
      exact no_triple_closedBalls ha hb hd huv.ge huz hvz hxu hxv hxz

theorem edge_inter_common_endpoint {u v w : ℂ} {a b c : ℝ}
    (hb : 0<b) (hc : 0<c) (huv : dist u v=a+b) (huw : dist u w=a+c)
    (hvw : b+c≤dist v w) : segment ℝ u v ∩ segment ℝ u w={u} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx,hy⟩
    have : x=u := by
      by_contra hxu
      have hx0 : x-u≠0 := sub_ne_zero.mpr hxu
      have Hv : SameRay ℝ (x-u) (v-u) := by
        simpa only [sub_add_sub_cancel'] using SameRay.rfl.add_right (sameRay_of_mem_segment hx)
      have Hw : SameRay ℝ (x-u) (w-u) := by
        simpa only [sub_add_sub_cancel'] using SameRay.rfl.add_right (sameRay_of_mem_segment hy)
      have Hr := Hv.symm.trans Hw (fun h=>(hx0 h).elim)
      have H:=Hr.norm_sub
      rw [sub_sub_sub_cancel_right,← dist_eq_norm,← dist_eq_norm,← dist_eq_norm,
        dist_comm v u,dist_comm w u,huv,huw] at H
      have habs : |a+b-(a+c)|<b+c := by rw [abs_lt]; constructor <;> linarith
      linarith
    exact this
  · rintro x rfl
    exact ⟨left_mem_segment ℝ x v,left_mem_segment ℝ x w⟩
end CannonTangentSegments

end
end
end
end

end OAI
