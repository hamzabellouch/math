import Mathlib
import OAI.Combinatorics.UniformKServer.LaminarTransport
import OAI.Combinatorics.UniformKServer.TreeLeaves

namespace OAI

                                    
section

/-! The laminar cuts of the literal finite tree; exact matching transport and
an occupied-endpoint separating edge below a deepest common ancestor. -/
noncomputable section
namespace UniformKServer.TreeAncestry
open Finset TreeRounding
open scoped Classical
variable {n : ℕ} {S : Shape n}

theorem comparable_depth {u v w : Vertex n} (hu : descends S u w)
    (hv : descends S v w) (hd : depth S u≤depth S v) : descends S u v := by
  obtain ⟨he,ha⟩ := ancestor_spec (depth S u) v hd
  have hh := same_ancestor (ha.trans hv) hu he
  exact hh ▸ ha

theorem subtree_laminar : LaminarTransport.Laminar (subtree S) := by
  intro u v
  by_cases h : ∃ w,descends S u w ∧ descends S v w
  · obtain ⟨w,hu,hv⟩ := h
    rcases le_total (depth S u) (depth S v) with hd|hd
    · right; left
      intro x hx
      simp only [subtree,mem_filter,mem_univ,true_and] at hx ⊢
      exact (comparable_depth hu hv hd).trans hx
    · left
      intro x hx
      simp only [subtree,mem_filter,mem_univ,true_and] at hx ⊢
      exact (comparable_depth hv hu hd).trans hx
  · right; right
    apply disjoint_left.mpr
    intro w hu hv
    exact h ⟨w,(mem_filter.mp hu).2,(mem_filter.mp hv).2⟩

def pathCost (w : Vertex n→ℝ) (u v : Vertex n) : ℝ :=
  ∑ c : Vertex n,if c=0 then 0 else
    w (S.parent c)*LaminarTransport.cross (subtree S c) u v

theorem matching {I : Type*} [Fintype I] (w : Vertex n→ℝ) (a b : I→Vertex n) :
    ∃ π : Equiv.Perm I,(∑ i,pathCost (S:=S) w (a i) (b (π i)))=
      ∑ c : Vertex n,if c=0 then 0 else w (S.parent c)*
        |LaminarTransport.mass (subtree S c) a-LaminarTransport.mass (subtree S c) b| := by
  obtain ⟨π,hπ⟩ := LaminarTransport.matching_exists (subtree S) a b subtree_laminar
  refine ⟨π,?_⟩
  unfold pathCost
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  by_cases hc : c=0
  · simp [hc]
  · simp only [ite_eq_right hc,←mul_sum]
    rw [show (∑ i,LaminarTransport.cross (subtree S c) (a i) (b (π i)))=
      |LaminarTransport.mass (subtree S c) a-LaminarTransport.mass (subtree S c) b| from hπ c]

theorem separating_edge (u v : Vertex n) (hne : u≠v) :
    ∃ p c : Vertex n,descends S p u ∧ descends S p v ∧ c≠0 ∧
      depth S c=depth S p+1 ∧
      ((descends S c u ∧ ¬descends S c v) ∨ (descends S c v ∧ ¬descends S c u)) := by
  let F : Finset (Vertex n) := univ.filter (fun p=>descends S p u ∧ descends S p v)
  have hF : F.Nonempty := ⟨0,mem_filter.mpr ⟨mem_univ _,TreeLeaves.root_descends _,TreeLeaves.root_descends _⟩⟩
  obtain ⟨p,hp,hmax⟩ := exists_max_image F (depth S) hF
  have hpu := (mem_filter.mp hp).2.1
  have hpv := (mem_filter.mp hp).2.2
  have hdeep : depth S p<depth S u ∨ depth S p<depth S v := by
    have h₁ := desc_depth hpu
    have h₂ := desc_depth hpv
    by_contra h
    push Not at h
    exact hne ((desc_same_depth hpu (by omega)).symm.trans (desc_same_depth hpv (by omega)))
  have make (a b : Vertex n) (ha : descends S p a) (hb : descends S p b)
      (hd : depth S p<depth S a)
      (hm : ∀ c,descends S c a → descends S c b → depth S c≤depth S p) :
      ∃ c : Vertex n,c≠0 ∧ depth S c=depth S p+1 ∧ descends S c a ∧ ¬descends S c b := by
    let c := ancestor S (depth S p+1) a
    have hc := ancestor_spec (S:=S) (depth S p+1) a (by omega)
    have hcdepth : depth S c=depth S p+1 := hc.1
    have h0 : c≠0 := by intro he; have hz : depth S c=0 := he ▸ depth_root; dsimp [c] at hz; omega
    refine ⟨c,h0,hcdepth,hc.2,?_⟩
    intro hh
    have h := hm c hc.2 hh
    omega
  rcases hdeep with hd|hd
  · obtain ⟨c,h0,hc,ha,hb⟩ := make u v hpu hpv hd (fun c ha hb=>hmax c (mem_filter.mpr ⟨mem_univ _,ha,hb⟩))
    exact ⟨p,c,hpu,hpv,h0,hc,Or.inl ⟨ha,hb⟩⟩
  · obtain ⟨c,h0,hc,ha,hb⟩ := make v u hpv hpu hd (fun c ha hb=>hmax c (mem_filter.mpr ⟨mem_univ _,hb,ha⟩))
    exact ⟨p,c,hpu,hpv,h0,hc,Or.inr ⟨ha,hb⟩⟩

theorem edge_le_path (w : Vertex n→ℝ) (hw : ∀ c,0≤w c) (u v c : Vertex n)
    (hc : c≠0) (hcut : (descends S c u ∧ ¬descends S c v) ∨ (descends S c v ∧ ¬descends S c u)) :
    w (S.parent c)≤pathCost (S:=S) w u v := by
  have he : LaminarTransport.cross (subtree S c) u v=1 := by
    rcases hcut with ⟨hu,hv⟩|⟨hv,hu⟩ <;>
      simp [LaminarTransport.cross,LaminarTransport.bit,subtree,hu,hv]
  have h := single_le_sum (s:=(univ : Finset (Vertex n)))
    (fun a _=>show 0≤(if a=0 then 0 else w (S.parent a)*LaminarTransport.cross (subtree S a) u v) from by
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (hw _) (abs_nonneg _)) (mem_univ c)
  simpa only [pathCost,ite_eq_right hc,he,mul_one] using h

end UniformKServer.TreeAncestry

end


end

end OAI
