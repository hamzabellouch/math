import Mathlib
import OAI.Combinatorics.TriangleRemoval.Spectral.CheckMarkedTraceCommon
import OAI.Combinatorics.TriangleRemoval.Process.PathRequiredBaseAppend

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
section JointPairHit
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem jointMarkedQuery_pair_hit (H : τ → Finset ι) (N d k : ℕ)
    (c : QueryCall ι τ) (path₁ path₂ : List (ι × τ)) (ν : τ → PMF (Fin N))
    {z : Bool × Bool × List (QueryCall ι τ)}
    (hz : z ∈ (ExposureTree.fresh ν
      (jointMarkedQuery H N
        (pairRequired (c.address.reverse ++ path₁) (c.address.reverse ++ path₂)) d k c)).support)
    (hp : ∃ a ∈ z.2.2, a.address = path₁.reverse ++ c.address)
    (hq : ∃ a ∈ z.2.2, a.address = path₂.reverse ++ c.address) : z.2.1 = true := by
  induction d generalizing k c path₁ path₂ z with
  | zero =>
    rw [jointMarkedQuery,ExposureTree.fresh_bind] at hz
    obtain ⟨_,_,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    have he : z = (true,true,[c]) := by
      simpa only [ExposureTree.fresh,PMF.mem_support_pure_iff] using hz
    rw [he]
  | succ d ih =>
    cases path₁ with
    | nil =>
      simp only [List.append_nil] at hz
      rw [jointMarkedQuery_pair_nil] at hz
      exact jointMarkedQuery_hit H N (d+1) k c path₂ ν hz hq
    | cons a as =>
      cases path₂ with
      | nil =>
        simp only [List.append_nil] at hz
        have he : pairRequired (c.address.reverse ++ a :: as) c.address.reverse =
            pairRequired c.address.reverse (c.address.reverse ++ a :: as) := by
          funext l
          exact Bool.or_comm _ _
        rw [he,jointMarkedQuery_pair_nil] at hz
        exact jointMarkedQuery_hit H N (d+1) k c (a :: as) ν hz hp
      | cons b bs =>
        rw [jointMarkedQuery,ExposureTree.fresh_bind] at hz
        obtain ⟨values,hvalues,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
        rw [ExposureTree.fresh_mapOutput] at hz
        obtain ⟨w,hw,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
        have hp' := query_trace_cons_hit_tail c w.2.2 a as hp
        have hq' := query_trace_cons_hit_tail c w.2.2 b bs hq
        let cs := values.mergeSort (fun a b => a.2.val ≤ b.2.val)
        let req := pairRequired (c.address.reverse ++ a :: as) (c.address.reverse ++ b :: bs)
        let program (p : (ι × τ) × Fin N) := if p.2.val < k then
          jointMarkedQuery H N req d p.2.val
            ⟨p.1 :: c.address,(H p.1.2).erase p.1.1,some p.1.2⟩
          else ExposureTree.done (false,false,[])
        have hnd : (cs.map Prod.fst).Nodup := by
          rw [← ExposureTree.freshLog_outcome] at hvalues
          obtain ⟨x,hx,hxe⟩ := (PMF.mem_support_map_iff _ _ _).mp hvalues
          have he := (ExposureTree.freshLog_exposeLabeled_support ν Prod.snd _ hx).1
          rw [hxe] at he
          apply ((List.mergeSort_perm values (fun a b => a.2.val ≤ b.2.val)).map Prod.fst).nodup_iff.mpr
          rw [he]
          exact Finset.nodup_toList _
        have hhead (v : ι × τ) (vs : List (ι × τ))
            (p : (ι × τ) × Fin N) (_ : p ∈ cs)
            (y : Bool × Bool × List (QueryCall ι τ))
            (hy : y ∈ (ExposureTree.fresh ν (program p)).support)
            (hh : ∃ q ∈ y.2.2, q.address = (v :: vs).reverse ++ c.address) : p.1 = v := by
          dsimp only [program] at hy
          split_ifs at hy with hk
          · exact jointMarkedQuery_hit_head H N d p.2.val req ν c.address p.1 v vs _ _ hy hh
          · have he : y = (false,false,[]) := by
              simpa only [ExposureTree.fresh,PMF.mem_support_pure_iff] using hy
            simp only [he,List.not_mem_nil,false_and,exists_false] at hh
        change w ∈ (ExposureTree.fresh ν (ExposureTree.checkMarkedTrace
          (cs.map (fun p => (req (p.1 :: c.address),program p))))).support at hw
        by_cases hab : a = b
        · subst b
          have hrow : cs.map (fun p => (req (p.1 :: c.address),program p)) =
              cs.map (fun p => (decide (p.1 = a),program p)) := by
            apply List.map_congr_left
            intro p _
            simp only [req,pairRequired_base_child,or_self]
          rw [hrow] at hw
          apply ExposureTree.checkMarkedTrace_common_hit ν
            (fun q : QueryCall ι τ => q.address = (a :: as).reverse ++ c.address)
            (fun q : QueryCall ι τ => q.address = (a :: bs).reverse ++ c.address)
            Prod.fst program a cs hnd (hhead a as) (hhead a bs) _ hw hp' hq'
          intro p hp y hy hpy hqy
          have hpa := hhead a as p hp y hy hpy
          dsimp only [program] at hy
          split_ifs at hy with hk
          · apply ih p.2.val
              ⟨p.1 :: c.address,(H p.1.2).erase p.1.1,some p.1.2⟩ as bs
            · simpa only [req,List.reverse_cons,List.append_assoc,List.singleton_append,hpa] using hy
            · simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,hpa] using hpy
            · simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,hpa] using hqy
          · have he : y = (false,false,[]) := by
              simpa only [ExposureTree.fresh,PMF.mem_support_pure_iff] using hy
            simp only [he,List.not_mem_nil,false_and,exists_false] at hpy
        · have hrow : cs.map (fun p => (req (p.1 :: c.address),program p)) =
              cs.map (fun p => (decide (p.1 = a ∨ p.1 = b),program p)) := by
            apply List.map_congr_left
            intro p _
            rw [show req (p.1 :: c.address) = decide (p.1 = a ∨ p.1 = b) from
              pairRequired_base_child c.address a b p.1 as bs]
          rw [hrow] at hw
          apply ExposureTree.checkMarkedTrace_two_hit ν
            (fun q : QueryCall ι τ => q.address = (a :: as).reverse ++ c.address)
            (fun q : QueryCall ι τ => q.address = (b :: bs).reverse ++ c.address)
            Prod.fst program a b hab cs hnd _ _ hw hp' hq'
          · intro p hp y hy hh
            have hpa := hhead a as p hp y hy hh
            refine ⟨hpa,?_⟩
            dsimp only [program,req] at hy
            split_ifs at hy with hk
            · simp only [hpa] at hy
              rw [jointMarkedQuery_pair_child H N d p.2.val c.address a b as bs hab] at hy
              apply jointMarkedQuery_hit H N d p.2.val
                ⟨a :: c.address,(H a.2).erase a.1,some a.2⟩ as ν hy
              simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hh
            · have he : y = (false,false,[]) := by
                simpa only [ExposureTree.fresh,PMF.mem_support_pure_iff] using hy
              simp only [he,List.not_mem_nil,false_and,exists_false] at hh
          · intro p hp y hy hh
            have hpb := hhead b bs p hp y hy hh
            refine ⟨hpb,?_⟩
            dsimp only [program,req] at hy
            split_ifs at hy with hk
            · simp only [hpb] at hy
              have he : pairRequired (c.address.reverse ++ a :: as) (c.address.reverse ++ b :: bs) =
                  pairRequired (c.address.reverse ++ b :: bs) (c.address.reverse ++ a :: as) := by
                funext l
                exact Bool.or_comm _ _
              rw [he,jointMarkedQuery_pair_child H N d p.2.val c.address b a bs as (Ne.symm hab)] at hy
              apply jointMarkedQuery_hit H N d p.2.val
                ⟨b :: c.address,(H b.2).erase b.1,some b.2⟩ bs ν hy
              simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hh
            · have he : y = (false,false,[]) := by
                simpa only [ExposureTree.fresh,PMF.mem_support_pure_iff] using hy
              simp only [he,List.not_mem_nil,false_and,exists_false] at hh

end JointPairHit
end SharpTerminalLeave

end

end OAI
