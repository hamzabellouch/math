import OAI.Combinatorics.HadwigerCounterexample.ReservedLabels

namespace OAI

/-! # Four Edge Families -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Finset Function
open scoped BigOperators
namespace StatusAnalysis
variable {A B : Rates} {I : Grid→Type} {L : Type} [DecidableEq L] [∀ i,DecidableEq (I i)]
namespace Guild
open Club
variable (C : Congress I A B L)

abbrev Bags (I : Grid→Type) := ∀ i,Finset (I i)
structure Parade (s : Straps L) (v : ∀ i,Suite A B i) (g : Bags I) (p : Finset Grid) : Prop where
  batch (i) (h : i∈p) :
    (C i).bundle (g i) s ∧ (C i).contents (g i)=v i∧ 1≤(g i).card∧(g i).card≤7
  mixed (i j) (hx : i∈p) (hy:j∈p) (he : i≠j) x (hX : x∈g i) y (hY : y∈g j) (b) :
    (C i).addr x b ≠ (C j).addr y b

set_option maxHeartbeats 800000 in
theorem full_parade (s : Straps L) {v : ∀ i,Suite A B i}
    (ht : ∀ i:Grid,(C i).travels s 100 (view _ _) (chapter C s i))
    (hv : ∀ i, v i∈chapter C s i) :
    ∃ g, Parade C s v g Finset.univ := by
  classical
  have he (p:Finset Grid) :
      ∃ g, Parade C s v g p := by
    induction p using Finset.induction_on with
    | empty =>
      exact ⟨fun _=>∅,⟨fun i hi=> (notMem_empty i hi).elim,
        fun i _ hi=> (notMem_empty i hi).elim⟩⟩
    | insert i p hi ih =>
      obtain ⟨g,hg⟩:=ih
      let Q (b : Bool) := p.biUnion (fun i=> (C i).addrs (g i) b)
      have hh (b) : (Q b).card≤28 := by
        have he (i:Grid) (h:i∈p) : ((C i).addrs (g i) b).card≤7 :=
          Finset.card_image_le.trans (hg.batch i h).2.2.2
        refine (Finset.card_biUnion_le).trans ((Finset.sum_le_sum he).trans ?_)
        have hh : p.card≤4 := p.card_le_univ.trans_eq (by simp [Grid,Nodes])
        simp only [Finset.sum_const,nsmul_eq_mul, Nat.cast_id]; omega
      let V:= chapter C s i
      have hr : (C i).travels (s⊔Q) 4 (view _ _) V := (C i).travel_more (ht i) Q hh (by norm_num)
      obtain ⟨t,ht,hT,hA,hB⟩:=fresh_single (C i) hr (v i) (hv i)
      let f:=update g i t
      have hC (j) (h:j∈p) (x : I j) (hx:x∈f j) (y : I i) (hy:y∈t) (b) :
          (C j).addr x b≠ (C i).addr y b := by
        intro hz
        apply ((ht.1 y hy).2 b)
        refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,h,?_⟩)
        unfold f at hx
        rw [Function.update_of_ne (show j ≠ i from fun e=>hi (e ▸ h))] at hx
        exact Finset.mem_image.mpr ⟨x,hx,hz⟩
      refine ⟨f,⟨fun j hj=>?_,fun j k hj hk he x hx y hy b=>?_⟩⟩
      · rcases Finset.mem_insert.mp hj with hj|hj
        · subst j; unfold f; rw [update_self]
          exact ⟨Club.bundle_back _ le_sup_left ht,hT,hA,hB⟩
        unfold f; rw [update_of_ne (show j ≠ i from fun h=>hi (h ▸ hj))]
        exact hg.batch j hj
      rcases Finset.mem_insert.mp hj with hj|hj
      · subst j; exact Ne.symm (hC k ((Finset.mem_insert.mp hk).resolve_left (Ne.symm he)) y hy x
          (by simpa only [f,update_self] using hx) b)
      rcases Finset.mem_insert.mp hk with hk|hk
      · subst k; exact hC j hj x hx y (by simpa only [f,update_self] using hy) b
      unfold f at hx hy
      rw [update_of_ne (show j ≠ i from fun h=>hi (h ▸ hj))] at hx
      rw [update_of_ne (show k ≠ i from fun h=>hi (h ▸ hk))] at hy
      exact hg.mixed j k hj hk he x hx y hy b
  exact he _
end Guild
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
