import Mathlib
import OAI.Geometry.Cannon.Modulus.BoundaryNormalizedAnnularCarriers
import OAI.Geometry.Cannon.Conformal.FinitePackingVertex

namespace OAI

section
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators OnePoint

namespace CannonRadialEnergy

lemma local_subdisk (c p : ℂ) {r R K : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) (hK : 0 ≤ K)
    (hnear : dist c p ≤ r+K*R) :
    ∃ q : ℂ,ball q (min r R)⊆ball c r ∧
      ball q (min r R)⊆ball p ((K+2)*R) := by
  let s:=min r R
  have hs : 0 ≤ s:=le_min hr hR
  have hsr : s ≤ r:=min_le_left _ _
  have hsR : s ≤ R:=min_le_right _ _
  have hn : ¬Disjoint (closedBall c (r-s)) (closedBall p (K*R+s)) := by
    rw [disjoint_closedBall_closedBall_iff (sub_nonneg.mpr hsr) (by positivity)]
    linarith
  obtain ⟨q,hqc,hqp⟩:=Set.not_disjoint_iff_nonempty_inter.mp hn
  refine ⟨q,?_,?_⟩
  · intro x hx
    have ht:=dist_triangle x q c
    have hx':=mem_ball.mp hx
    have hq':=mem_closedBall.mp hqc
    apply mem_ball.mpr
    linarith
  · intro x hx
    have ht:=dist_triangle x q p
    have hx':=mem_ball.mp hx
    have hq':=mem_closedBall.mp hqp
    apply mem_ball.mpr
    nlinarith

theorem local_disjoint_disk_square_budget {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (r : ι → ℝ) (p : ℂ) {R K : ℝ}
    (hr : ∀ i,0 ≤ r i) (hR : 0 ≤ R) (hK : 0 ≤ K)
    (hdisj : Pairwise (fun i j=> Disjoint (ball (c i) (r i)) (ball (c j) (r j))))
    (hnear : ∀ i,dist (c i) p ≤ r i+K*R) :
    (∑ i,(min (r i) R)^2) ≤ (K+2)^2*R^2 := by
  choose q hqc hqp using fun i=> local_subdisk (c i) p (hr i) hR hK (hnear i)
  have h:=disjoint_disk_square_budget q (fun i=> min (r i) R) p
    (fun i=> le_min (hr i) hR) (by positivity)
    (fun i j hij=> (hdisj hij).mono (hqc i) (hqc j)) hqp
  convert h using 1
  ring

theorem active_local_disk_square_budget {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (r : ι → ℝ) (p : ℂ) (active : ι → Prop) [DecidablePred active]
    {R K : ℝ} (hr : ∀ i,0 ≤ r i) (hR : 0 ≤ R) (hK : 0 ≤ K)
    (hdisj : Pairwise (fun i j=> Disjoint (ball (c i) (r i)) (ball (c j) (r j))))
    (hnear : ∀ i,active i → dist (c i) p ≤ r i+K*R) :
    (∑ i,if active i then (min (r i) R)^2 else 0) ≤ (K+2)^2*R^2 := by
  have h:=local_disjoint_disk_square_budget (fun i : {i // active i}=> c i)
    (fun i=> r i) p (fun i=> hr i) hR hK
    (fun i j hij=> hdisj (Subtype.val_injective.ne hij)) (fun i=> hnear i i.property)
  have he : (∑ i ∈ Finset.univ.filter active,(min (r i) R)^2)=
      ∑ i : {i // active i},(min (r i) R)^2 :=
    Finset.sum_subtype _ (by simp) _
  rw [←he,Finset.sum_filter] at h
  exact h

end CannonRadialEnergy

namespace CannonLocalPacking
attribute [local instance] Classical.propDecidable

lemma compact_subset_closedBall_of_frontier_subset {K : Set ℂ} (hK : IsCompact K)
    (c : ℂ) (R : ℝ) (hfront : frontier K ⊆ closedBall c R) :
    K ⊆ closedBall c R := by
  intro z hz
  have hd : DiffContOnCl ℂ (fun w : ℂ=>w-c) K :=
    (differentiable_id.sub_const c).diffContOnCl
  have h:=Complex.norm_le_of_forall_mem_frontier_norm_le hK.isBounded hd
    (fun w hw=>by simpa only [mem_closedBall,dist_eq_norm] using hfront hw)
    (subset_closure hz)
  simpa only [mem_closedBall,dist_eq_norm] using h

lemma tile_ball_dichotomy {K : Set ℂ} (hK : IsClosed K) (p : ℂ) (R : ℝ)
    (hmeet : (K∩closedBall p R).Nonempty) :
    (frontier K∩closedBall p R).Nonempty ∨ closedBall p R ⊆ interior K := by
  by_cases hf : (frontier K∩closedBall p R).Nonempty
  · exact Or.inl hf
  right
  have hsub : closedBall p R ⊆ interior K∪Kᶜ := by
    intro x hx
    by_cases hxK : x∈K
    · left
      by_contra hn
      exact hf ⟨x,⟨subset_closure hxK,hn⟩,hx⟩
    · exact Or.inr hxK
  obtain hi|ho:=(convex_closedBall p R).isPreconnected.subset_or_subset
    isOpen_interior hK.isOpen_compl
    (disjoint_compl_right.mono interior_subset Subset.rfl) hsub
  · exact hi
  · obtain ⟨x,hxK,hxp⟩:=hmeet
    exact (ho hxp hxK).elim

lemma tile_max_disk_control {ν : Type*} (c : ν → ℂ) (r : ν → ℝ)
    (V : Set ν) (s : ν) {K : Set ℂ} (hK : IsCompact K)
    (hmax : ∀ j∈V,r j ≤ r s)
    (hpair : ∀ j∈V,dist (c j) (c s) ≤ r j+r s)
    (hfront : ∀ x∈frontier K,∃ j∈V,x∈closedBall (c j) (r j)) :
    K⊆closedBall (c s) (3*r s) := by
  apply compact_subset_closedBall_of_frontier_subset hK
  intro x hx
  obtain ⟨j,hj,hxj⟩:=hfront x hx
  have ht:=dist_triangle x (c j) (c s)
  have hm:=hmax j hj
  have hp:=hpair j hj
  have hxj':=mem_closedBall.mp hxj
  apply mem_closedBall.mpr
  linarith

lemma frontier_disk_charge {ν : Type*} (c : ν → ℂ) (r : ν → ℝ)
    (V : Set ν) (s : ν) (hs : s∈V) (p : ℂ) {R : ℝ}
    (hpair : ∀ j∈V,dist (c j) (c s) ≤ r j+r s)
    {K : Set ℂ} (hfront : ∀ x∈frontier K,∃ j∈V,x∈closedBall (c j) (r j))
    (hmeet : (frontier K∩closedBall p R).Nonempty) :
    ∃ j∈V,dist (c j) p ≤ r j+3*R ∧ min (r s) R ≤ min (r j) R := by
  obtain ⟨x,hxK,hxp⟩:=hmeet
  obtain ⟨j,hj,hxj⟩:=hfront x hxK
  have hxp':=mem_closedBall.mp hxp
  have hxj':=mem_closedBall.mp hxj
  by_cases hjR : r j ≤ R
  · refine ⟨s,hs,?_,le_rfl⟩
    have ht:=dist_triangle (c s) (c j) p
    have ht':=dist_triangle (c j) x p
    have hp:=hpair j hj
    rw [dist_comm (c j) (c s)] at hp
    rw [dist_comm (c j) x] at ht'
    linarith
  · refine ⟨j,hj,?_,?_⟩
    · have ht:=dist_triangle (c j) x p
      rw [dist_comm (c j) x] at ht
      have hR : 0 ≤ R:=(dist_nonneg.trans hxp')
      linarith
    · rw [min_eq_right (le_of_not_ge hjR)]
      exact min_le_right _ _

lemma clipped_tile_control {ν : Type*} (c : ν → ℂ) (r : ν → ℝ)
    (V : Set ν) (s : ν) {K : Set ℂ} (hK : IsCompact K)
    (hmax : ∀ j∈V,r j ≤ r s)
    (hpair : ∀ j∈V,dist (c j) (c s) ≤ r j+r s)
    (hfront : ∀ x∈frontier K,∃ j∈V,x∈closedBall (c j) (r j))
    (p : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    K∩closedBall p R⊆closedBall (if r s ≤ R then c s else p) (3*min (r s) R) := by
  by_cases hr : r s ≤ R
  · rw [ite_eq_left hr,min_eq_left hr]
    exact inter_subset_left.trans (tile_max_disk_control c r V s hK hmax hpair hfront)
  · rw [ite_eq_right hr,min_eq_right (le_of_not_ge hr)]
    exact inter_subset_right.trans (closedBall_subset_closedBall (by linarith))

end CannonLocalPacking

namespace CannonLocalPacking
attribute [local instance] Classical.propDecidable

lemma sum_indicator_le_one {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P]
    {A : ℝ} (hA : 0 ≤ A) (hP : ∀ i j,P i → P j → i=j) :
    (∑ i,if P i then A else 0) ≤ A := by
  classical
  by_cases h : ∃ i,P i
  · obtain ⟨i,hi⟩:=h
    have he : (∑ j,if P j then A else 0)=A := by
      rw [Finset.sum_eq_single i]
      · simp [hi]
      · intro j _ hji
        have hj : ¬P j:=fun hj=>hji (hP j i hj hi)
        simp [hj]
      · simp
    exact he.le
  · have hn : ∀ i,¬P i:=by simpa only [not_exists] using h
    simpa [hn] using hA

lemma incidence_sum_le {κ ν : Type*} [Fintype κ] [Fintype ν] [DecidableEq ν]
    (V : κ → Finset ν) (g : ν → ℝ) (hg : ∀ j,0 ≤ g j) (D : ℕ)
    (hinc : ∀ j,(Finset.univ.filter (fun d=>j∈V d)).card ≤ D) :
    (∑ d,∑ j∈V d,g j) ≤ (D:ℝ)*∑ j,g j := by
  classical
  have hs (d : κ) : (∑ j∈V d,g j)=∑ j,if j∈V d then g j else 0 := by simp
  simp_rw [hs]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hinc j) (hg j)

theorem local_active_tile_square_budget {κ ν : Type*} [Fintype κ] [Fintype ν]
    [DecidableEq ν] (c : ν → ℂ) (r : ν → ℝ) (hr : ∀ j,0 ≤ r j)
    (V : κ → Finset ν) (s : κ → ν) (hs : ∀ d,s d∈V d)
    (K : κ → Set ℂ) (hclosed : ∀ d,IsClosed (K d))
    (htile : Pairwise (fun d e=>Disjoint (interior (K d)) (interior (K e))))
    (hpair : ∀ d,∀ j∈V d,dist (c j) (c (s d)) ≤ r j+r (s d))
    (hfront : ∀ d,∀ x∈frontier (K d),∃ j∈V d,x∈closedBall (c j) (r j))
    (hdisj : Pairwise (fun i j=>Disjoint (ball (c i) (r i)) (ball (c j) (r j))))
    (p : ℂ) {R : ℝ} (hR : 0 ≤ R) (D : ℕ)
    (hinc : ∀ j,(Finset.univ.filter (fun d=>j∈V d)).card ≤ D) :
    (∑ d,if (K d∩closedBall p R).Nonempty then (min (r (s d)) R)^2 else 0) ≤
      (25*(D:ℝ)+1)*R^2 := by
  classical
  let near : ν → Prop:=fun j=>dist (c j) p ≤ r j+3*R
  let g : ν → ℝ:=fun j=>if near j then (min (r j) R)^2 else 0
  let whole : κ → Prop:=fun d=>closedBall p R⊆interior (K d)
  have hg : ∀ j,0 ≤ g j:=by intro j; dsimp [g]; split_ifs <;> positivity
  have hnear : (∑ j,g j) ≤ 25*R^2 := by
    have hh:=CannonRadialEnergy.active_local_disk_square_budget c r p near hr hR
      (show (0:ℝ) ≤ 3 by norm_num) hdisj (fun _ hj=>hj)
    norm_num [g] at hh ⊢
    exact hh
  have hw : (∑ d,if whole d then R^2 else 0) ≤ R^2 := by
    apply sum_indicator_le_one whole (sq_nonneg R)
    intro d e hd he
    by_contra hde
    have hpd:=hd (mem_closedBall_self hR)
    have hpe:=he (mem_closedBall_self hR)
    exact Set.disjoint_left.mp (htile hde) hpd hpe
  have hf (d : κ) :
      (if (K d∩closedBall p R).Nonempty then (min (r (s d)) R)^2 else 0) ≤
        (∑ j∈V d,g j)+(if whole d then R^2 else 0) := by
    have hsg : 0 ≤ ∑ j∈V d,g j:=Finset.sum_nonneg (fun j _=>hg j)
    have hwi : 0 ≤ if whole d then R^2 else 0:=by split_ifs <;> positivity
    by_cases ha : (K d∩closedBall p R).Nonempty
    · rw [ite_eq_left ha]
      obtain hb|hb:=tile_ball_dichotomy (hclosed d) p R ha
      · obtain ⟨j,hj,hjn,hle⟩:=frontier_disk_charge c r (V d) (s d) (hs d) p
          (hpair d) (hfront d) hb
        have hle': (min (r (s d)) R)^2 ≤ (min (r j) R)^2:=
          pow_le_pow_left₀ (le_min (hr _) hR) hle 2
        have hgj : g j=(min (r j) R)^2:=ite_eq_left hjn
        have hsum:=Finset.single_le_sum (fun j _=>hg j) hj
        rw [hgj] at hsum
        exact (hle'.trans hsum).trans (le_add_of_nonneg_right hwi)
      · have hb' : whole d:=hb
        rw [ite_eq_left hb']
        have hle:=pow_le_pow_left₀ (le_min (hr (s d)) hR) (min_le_right (r (s d)) R) 2
        exact hle.trans (le_add_of_nonneg_left hsg)
    · rw [ite_eq_right ha]
      exact add_nonneg hsg hwi
  calc
    _ ≤ ∑ d,((∑ j∈V d,g j)+(if whole d then R^2 else 0)) :=
      Finset.sum_le_sum (fun d _=>hf d)
    _ = (∑ d,∑ j∈V d,g j)+(∑ d,if whole d then R^2 else 0) := Finset.sum_add_distrib
    _ ≤ (D:ℝ)*(∑ j,g j)+R^2 := add_le_add (incidence_sum_le V g hg D hinc) hw
    _ ≤ (D:ℝ)*(25*R^2)+R^2 := by gcongr
    _ = _ := by ring

end CannonLocalPacking

namespace CannonTileTopology
open CannonLocalPacking

attribute [local instance] Classical.propDecidable

theorem selected_tile_budget {κ ν : Type*} [Fintype κ] [Fintype ν] [DecidableEq ν]
    (V : κ → Finset ν) (hV : ∀ d,(V d).Nonempty) (pole : ν)
    (K : κ → Set ℂ) (hc : ∀ d,pole∉V d → IsCompact (K d))
    (hd : Pairwise fun d e=>Disjoint (interior (K d)) (interior (K e)))
    (c : ν → ℂ) (r : ν → ℝ) (hr : ∀ j,0≤r j)
    (hdisj : Pairwise fun i j=>Disjoint (ball (c i) (r i)) (ball (c j) (r j)))
    (hfront : ∀ d,pole∉V d → ∀ x∈frontier (K d),∃ j∈V d,x∈closedBall (c j) (r j))
    (hpair : ∀ d,pole∉V d → ∀ i∈V d,∀ j∈V d,dist (c i) (c j)≤r i+r j)
    (D : ℕ) (hinc : ∀ j,(Finset.univ.filter (fun d=>j∈V d)).card≤D) :
    ∃ s : κ → ν,(∀ d,s d∈V d) ∧
      (∀ d,pole∉V d → K d⊆closedBall (c (s d)) (3*r (s d))) ∧
      (∀ p : ℂ,∀ R : ℝ,0≤R →
        (∑ d,if pole∉V d ∧ (K d∩closedBall p R).Nonempty then (min (r (s d)) R)^2 else 0)
          ≤(25*(D:ℝ)+1)*R^2) ∧
      (Finset.univ.filter (fun d=>¬pole∉V d)).card≤D := by
  classical
  have hm (d : κ) : ∃ j∈V d,∀ i∈V d,r i≤r j := Finset.exists_max_image (V d) r (hV d)
  choose s hs hm using hm
  refine ⟨s,hs,?_,?_,?_⟩
  · intro d hdp
    exact tile_max_disk_control c r (V d) (s d) (hc d hdp) (hm d)
      (fun j hj=>hpair d hdp j hj (s d) (hs d)) (hfront d hdp)
  · intro p R hR
    let good : κ → Prop:=fun d=>pole∉V d
    have hi (j : ν) :
        (Finset.univ.filter (fun d : {d // good d}=>j∈V d.val)).card≤D := by
      have he : (Finset.univ.filter (fun d : {d // good d}=>j∈V d.val)).card=
          (Finset.univ.filter (fun d : κ=>good d ∧ j∈V d)).card := by
        apply Finset.card_bij (fun d _=>d.val)
        · intro d hd
          simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hd ⊢
          exact ⟨d.property,hd⟩
        · intro d hd e he hde
          exact Subtype.ext hde
        · intro d hd
          simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hd
          exact ⟨⟨d,hd.1⟩,by simpa using hd.2,rfl⟩
      rw [he]
      apply (Finset.card_le_card (show Finset.univ.filter (fun d=>good d ∧ j∈V d)⊆
        Finset.univ.filter (fun d=>j∈V d) from ?_)).trans (hinc j)
      intro d hd
      simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using
        (Finset.mem_filter.mp hd).2.2
    have hh:=local_active_tile_square_budget c r hr (fun d : {d // good d}=>V d.val)
      (fun d=>s d.val) (fun d=>hs d.val) (fun d=>K d.val) (fun d=>(hc d.val d.property).isClosed)
      (fun d e hde=>hd (Subtype.val_injective.ne hde))
      (fun d j hj=>hpair d.val d.property j hj (s d.val) (hs d.val))
      (fun d=>hfront d.val d.property) hdisj p hR D hi
    have he : (∑ d∈Finset.univ.filter good,
        if (K d∩closedBall p R).Nonempty then (min (r (s d)) R)^2 else 0)=
        ∑ d : {d // good d},if (K d.val∩closedBall p R).Nonempty then (min (r (s d.val)) R)^2 else 0 :=
      Finset.sum_subtype _ (by simp) _
    rw [←he,Finset.sum_filter] at hh
    simpa only [good,ite_and] using hh
  · simpa only [not_not] using hinc pole
end CannonTileTopology

namespace CannonTileTopology
open Topology CannonMobius

attribute [local instance] Classical.propDecidable

theorem pole_chart_tile_budget {κ ν : Type*} [Fintype κ] [Fintype ν] [DecidableEq ν]
    (V : κ → Finset ν) (hV : ∀ d,(V d).Nonempty) (pole : ν)
    (K : κ → Set (OnePoint ℂ)) (hclosed : ∀ d,IsClosed (K d))
    (hd : Pairwise fun d e=>Disjoint (interior (K d)) (interior (K e)))
    (z : ν → ℂ) (ρ : ν → ℝ) (hρ : ∀ j,0<ρ j)
    (hsep : ∀ i j,i≠j → ρ i+ρ j≤dist (z i) (z j))
    (hfront : ∀ d,frontier (K d)⊆⋃ j∈V d,((↑) '' closedBall (z j) (ρ j) : Set (OnePoint ℂ)))
    (hpair : ∀ d,∀ i∈V d,∀ j∈V d,i≠j → dist (z i) (z j)=ρ i+ρ j)
    (hpinc : ∀ d,(z pole:OnePoint ℂ)∈K d → pole∈V d)
    (N : OnePoint ℂ ≃ₜ OnePoint ℂ) (hN : N∈biholomorphic) (hpole : N (z pole)=∞)
    (D : ℕ) (hinc : ∀ j,(Finset.univ.filter (fun d=>j∈V d)).card≤D) :
    let T : κ → Set ℂ:=fun d=>((↑) : ℂ → OnePoint ℂ) ⁻¹' (N '' K d)
    ∃ c : κ → ℂ,∃ r : κ → ℝ,∃ s : κ → ν,
      (∀ d,s d∈V d) ∧ (∀ d,0≤r d) ∧
      (∀ d,pole∉V d → T d⊆closedBall (c d) (3*r d)) ∧
      (∀ p : ℂ,∀ R : ℝ,0≤R →
        (∑ d,if pole∉V d ∧ (T d∩closedBall p R).Nonempty then (min (r d) R)^2 else 0)
          ≤(25*(D:ℝ)+1)*R^2) ∧
      (Finset.univ.filter (fun d=>¬pole∉V d)).card≤D := by
  classical
  dsimp only
  let T : κ → Set ℂ:=fun d=>((↑) : ℂ → OnePoint ℂ) ⁻¹' (N '' K d)
  obtain ⟨c₀,r₀,hr₀,hb₀,hc₀,hd₀⟩:=finite_packing_at_vertex z ρ hρ hsep N hN pole hpole
  let c : ν → ℂ:=fun j=>if h:j=pole then 0 else c₀ ⟨j,h⟩
  let r : ν → ℝ:=fun j=>if h:j=pole then 0 else r₀ ⟨j,h⟩
  have hr (j : ν) : 0≤r j := by
    dsimp [r]
    split_ifs with h
    · exact le_rfl
    · exact (hr₀ ⟨j,h⟩).le
  have hc (j : ν) (hj : j≠pole) :
      N '' ((↑) '' closedBall (z j) (ρ j) : Set (OnePoint ℂ))=(↑) '' closedBall (c j) (r j) := by
    simpa only [c,r,dite_eq_right hj] using hc₀ ⟨j,hj⟩
  have hdisj : Pairwise fun i j=>Disjoint (ball (c i) (r i)) (ball (c j) (r j)) := by
    intro i j hij
    by_cases hi : i=pole
    · simp [r,hi]
    by_cases hj : j=pole
    · simp [r,hj]
    simpa only [c,r,dite_eq_right hi,dite_eq_right hj] using
      hd₀ (show (⟨i,hi⟩ : {j // j≠pole})≠⟨j,hj⟩ from fun h=>hij (congrArg Subtype.val h))
  have hTc (d : κ) (hdp : pole∉V d) : IsCompact (T d) := by
    apply compact_trace (N.isClosedMap _ (hclosed d))
    rintro ⟨x,hx,he⟩
    have hex : x=(z pole:OnePoint ℂ):=N.injective (he.trans hpole.symm)
    subst x
    exact hdp (hpinc d hx)
  have hTd : Pairwise fun d e=>Disjoint (interior (T d)) (interior (T e)) := by
    intro d e hde
    have hh := (hd hde).image N.injective.injOn (subset_univ _) (subset_univ _)
    rw [N.image_interior,N.image_interior] at hh
    have hh':=hh.preimage ((↑) : ℂ → OnePoint ℂ)
    rw [OnePoint.isOpenMap_coe.preimage_interior_eq_interior_preimage OnePoint.continuous_coe,
      OnePoint.isOpenMap_coe.preimage_interior_eq_interior_preimage OnePoint.continuous_coe] at hh'
    exact hh'
  have hTf (d : κ) (hdp : pole∉V d) :
      ∀ x∈frontier (T d),∃ j∈V d,x∈closedBall (c j) (r j) := by
    intro x hx
    rw [show frontier (T d)=((↑) : ℂ → OnePoint ℂ) ⁻¹' frontier (N '' K d) from trace_frontier _,
      ←N.image_frontier] at hx
    obtain ⟨y,hy,hey⟩:=hx
    obtain ⟨j,hj,u,hu,heu⟩:=mem_iUnion₂.mp (hfront d hy)
    have hjp : j≠pole:=fun h=>hdp (h ▸ hj)
    have hh : (x:OnePoint ℂ)∈N '' ((↑) '' closedBall (z j) (ρ j) : Set (OnePoint ℂ)):=
      ⟨y,⟨u,hu,heu⟩,hey⟩
    rw [hc j hjp] at hh
    obtain ⟨v,hv,hev⟩:=hh
    have hvx : v=x:=OnePoint.coe_injective hev
    exact ⟨j,hj,hvx ▸ hv⟩
  have hTp (d : κ) (hdp : pole∉V d) :
      ∀ i∈V d,∀ j∈V d,dist (c i) (c j)≤r i+r j := by
    intro i hi j hj
    by_cases hij : i=j
    · subst j
      simp only [dist_self]
      exact add_nonneg (hr i) (hr i)
    exact transformed_disks_touch N (hρ i) (hρ j) (hpair d i hi j hj hij)
      (hc i (fun h=>hdp (h ▸ hi))) (hc j (fun h=>hdp (h ▸ hj)))
  obtain ⟨s,hs,hcell,hbud,hbad⟩:=selected_tile_budget V hV pole T hTc hTd c r hr hdisj hTf hTp D hinc
  exact ⟨(fun d=>c (s d)),(fun d=>r (s d)),s,hs,(fun d=>hr (s d)),hcell,hbud,hbad⟩
end CannonTileTopology

end
end

end OAI
