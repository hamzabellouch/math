import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.PathRequired
import OAI.Combinatorics.TriangleRemoval.Queries.JointMarkedQuery

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

lemma pathRequired_base_child {A : Type*} [DecidableEq A]
    (base : List A) (a p : A) (as : List A) :
    pathRequired (base.reverse ++ a :: as) (p :: base) = decide (p = a) := by
  simp [pathRequired,List.reverse_cons,List.prefix_append_right_inj]

lemma pathRequired_base_nil {A : Type*} [DecidableEq A]
    (base : List A) (p : A) : pathRequired base.reverse (p :: base) = false := by
  simp only [pathRequired,decide_eq_false_iff_not]
  intro h
  have hl := h.length_le
  simp only [List.length_reverse,List.length_cons] at hl
  omega

section MarkedTraceHit
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem jointMarkedQuery_hit (H : τ → Finset ι) (N d k : ℕ)
    (c : QueryCall ι τ) (path : List (ι × τ)) (ν : τ → PMF (Fin N))
    {z : Bool × Bool × List (QueryCall ι τ)}
    (hz : z ∈ (ExposureTree.fresh ν
      (jointMarkedQuery H N (pathRequired (c.address.reverse ++ path)) d k c)).support)
    (hhit : ∃ a ∈ z.2.2, a.address = path.reverse ++ c.address) : z.2.1 = true := by
  induction d generalizing k c path z with
  | zero =>
    rw [jointMarkedQuery,ExposureTree.fresh_bind] at hz
    obtain ⟨_,_,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    have he : z = (true,true,[c]) := by
      simpa only [ExposureTree.fresh,PMF.mem_support_pure_iff] using hz
    rw [he]
  | succ d ih =>
    rw [jointMarkedQuery,ExposureTree.fresh_bind] at hz
    obtain ⟨values,hvalues,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    rw [ExposureTree.fresh_mapOutput] at hz
    obtain ⟨w,hw,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    cases path with
    | nil =>
      apply ExposureTree.checkMarkedTrace_no_demands ν _ _ hw
      apply List.any_eq_false.mpr
      intro x hx
      obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
      simp only [List.append_nil,pathRequired_base_nil,Bool.false_eq_true,not_false_eq_true]
    | cons a as =>
      have hhit' : ∃ q ∈ w.2.2, q.address = (a :: as).reverse ++ c.address := by
        obtain ⟨q,hq,he⟩ := hhit
        rcases List.mem_cons.mp hq with rfl | hq
        · have hl := congrArg List.length he
          simp only [List.length_append,List.length_reverse,List.length_cons] at hl
          omega
        · exact ⟨q,hq,he⟩
      have hvals : (values.map Prod.fst).Nodup := by
        rw [← ExposureTree.freshLog_outcome] at hvalues
        obtain ⟨x,hx,hxe⟩ := (PMF.mem_support_map_iff _ _ _).mp hvalues
        have he := (ExposureTree.freshLog_exposeLabeled_support ν Prod.snd _ hx).1
        rw [hxe] at he
        rw [he]
        exact Finset.nodup_toList _
      have hsorted := ((List.mergeSort_perm values
        (fun a b => a.2.val ≤ b.2.val)).map Prod.fst).nodup_iff.mpr hvals
      have hpair : (values.mergeSort (fun a b => a.2.val ≤ b.2.val)).Pairwise
          (fun p q => p.1 ≠ q.1) := by
        simpa only [List.Nodup,List.pairwise_map] using hsorted
      apply (ExposureTree.checkMarkedTrace_one_hit ν
        (fun q : QueryCall ι τ => q.address = (a :: as).reverse ++ c.address) _ _ _ hw hhit').2
      · apply List.pairwise_map.mpr
        apply hpair.imp
        intro p q hpq hp
        simp only [pathRequired_base_child,decide_eq_true_eq] at hp
        simp only [pathRequired_base_child,decide_eq_false_iff_not]
        exact fun hq => hpq (hp.trans hq.symm)
      · intro child hchild y hy hhit
        obtain ⟨p,_,rfl⟩ := List.mem_map.mp hchild
        split_ifs at hy with hp
        · obtain ⟨q,hq,he⟩ := hhit
          have had := jointMarkedQuery_address H N _ d p.2.val
            ⟨p.1 :: c.address,(H p.1.2).erase p.1.1,some p.1.2⟩ ν hy q hq
          rw [he] at had
          have haa : a :: c.address <:+ (a :: as).reverse ++ c.address := by
            simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
            exact List.suffix_append _ _
          have hpa : p.1 = a := List.cons.inj
            ((List.suffix_of_suffix_length_le had haa (by simp)).eq_of_length (by simp)) |>.1
          refine ⟨?_,?_⟩
          · simp only [pathRequired_base_child,hpa,decide_true]
          · have hi := ih p.2.val
              ⟨p.1 :: c.address,(H p.1.2).erase p.1.1,some p.1.2⟩ as
              (by simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,hpa] using hy)
              (by simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,hpa] using
                (show ∃ q ∈ y.2.2, q.address = (a :: as).reverse ++ c.address from ⟨q,hq,he⟩))
            exact hi
        · have he : y = (false,false,[]) := by
            simpa only [ExposureTree.fresh,PMF.mem_support_pure_iff] using hy
          simp only [he,List.not_mem_nil,false_and,exists_false] at hhit

end MarkedTraceHit
end SharpTerminalLeave

end

end OAI
