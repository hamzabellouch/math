import Mathlib

namespace OAI

section
noncomputable section
namespace CannonTileTopology
open Set Metric Topology
open scoped OnePoint

lemma tangent_disk_meet {a b : ℂ} {r s : ℝ} (hr : 0<r) (hs : 0<s)
    (hd : dist a b=r+s) : (closedBall a r∩closedBall b s).Nonempty := by
  let q:=AffineMap.lineMap a b (r/(r+s))
  have hsum : 0<r+s:=add_pos hr hs
  have ht : 0≤r/(r+s):=div_nonneg hr.le hsum.le
  have ht' : r/(r+s)≤1:=(div_le_one hsum).mpr (by linarith)
  refine ⟨q,?_,?_⟩
  · change dist q a≤r
    dsimp [q]
    rw [dist_lineMap_left,Real.norm_eq_abs,abs_of_nonneg ht,hd,div_mul_cancel₀ _ hsum.ne']
  · change dist q b ≤ s
    dsimp [q]
    rw [dist_lineMap_right,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr ht'),hd]
    have he : (1-r/(r+s))*(r+s)=s:=by field_simp; ring
    exact he.le

lemma transformed_disks_touch (N : OnePoint ℂ ≃ₜ OnePoint ℂ)
    {a b a' b' : ℂ} {r s r' s' : ℝ} (hr : 0<r) (hs : 0<s)
    (hd : dist a b=r+s)
    (ha : N '' ((↑) '' closedBall a r : Set (OnePoint ℂ))=(↑) '' closedBall a' r')
    (hb : N '' ((↑) '' closedBall b s : Set (OnePoint ℂ))=(↑) '' closedBall b' s') :
    dist a' b'≤r'+s' := by
  obtain ⟨q,hqa,hqb⟩:=tangent_disk_meet hr hs hd
  have ha' : N (q:OnePoint ℂ)∈((↑) '' closedBall a' r' : Set (OnePoint ℂ)):=
    ha ▸ ⟨(q:OnePoint ℂ),⟨q,hqa,rfl⟩,rfl⟩
  have hb' : N (q:OnePoint ℂ)∈((↑) '' closedBall b' s' : Set (OnePoint ℂ)):=
    hb ▸ ⟨(q:OnePoint ℂ),⟨q,hqb,rfl⟩,rfl⟩
  obtain ⟨u,hu,heu⟩:=ha'
  obtain ⟨v,hv,hev⟩:=hb'
  have huv : u=v:=OnePoint.coe_injective (heu.trans hev.symm)
  subst v
  have ht:=dist_triangle a' u b'
  rw [dist_comm a' u] at ht
  exact ht.trans (add_le_add hu hv)

lemma packing_balls_disjoint {ν : Type*} (z : ν → ℂ) (r : ν → ℝ)
    (hsep : ∀ i j,i≠j → r i+r j≤dist (z i) (z j)) :
    Pairwise fun i j=>Disjoint (ball (z i) (r i)) (ball (z j) (r j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro q hqi hqj
  have h1:=mem_ball.mp hqi
  have h2:=mem_ball.mp hqj
  have ht:=dist_triangle (z i) q (z j)
  rw [dist_comm (z i) q] at ht
  have hs:=hsep i j hij
  linarith
end CannonTileTopology

end
end

end OAI
