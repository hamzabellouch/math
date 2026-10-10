import Mathlib
import OAI.Combinatorics.KMedian.Machines.CutLaws

namespace OAI

section Inline_PCPPathTable
namespace MetricKMedian.PCP.Compiler.PowerProgram
open scoped Classical

variable {D A : Type} [Fintype D] [Fintype A] [Inhabited A] [DecidableEq A]
def Test (cap : ℕ) (n : Fin (cap+1)) (w back : Fin cap → D)
    (rels : Fin cap → Finset (A × A)) (b c : Advice D A cap) : Prop :=
  ∀ (i j : Fin (cap+1)) (h : n.val=i.val+(j.val+1)),
    (b.get i.val (fun k => w ⟨k.val,by omega⟩),
     c.get j.val (fun k => back ⟨i.val+1+k.rev.val,by have := k.rev.isLt; omega⟩)) ∈
       rels ⟨i.val,by omega⟩
noncomputable def relation (cap : ℕ) (n : Fin (cap+1)) (w back : Fin cap → D)
    (rels : Fin cap → Finset (A × A)) : Finset (Advice D A cap × Advice D A cap) :=
  Finset.univ.filter (fun bc => Test cap n w back rels bc.1 bc.2)
variable {V : Type} [Fintype V] [Nonempty V] [Nonempty D]
  {G : PortGraph V D} (C : PortCSP G A)
omit [Fintype D] [Fintype A] [DecidableEq A] [Fintype V] [Nonempty V] [Nonempty D] in
lemma cut_prefix (cap i j : ℕ) (h : i+(j+1)≤cap) (p : G.Walk cap) (b c : Advice D A cap) :
    C.CutAccept i j (p.segment 0 (i+(j+1)) (by omega)) b c ↔
    (b.get i (fun k => p.port ⟨k.val,by omega⟩),
     c.get j (fun k => G.back (p.vertex ⟨i+1+k.rev.val,by have := k.rev.isLt; omega⟩)
       (p.port ⟨i+1+k.rev.val,by have := k.rev.isLt; omega⟩))) ∈
      C.allowed (p.vertex ⟨i,by omega⟩,p.port ⟨i,by omega⟩) := by
  rw [C.cut_literal]
  simp only [PortGraph.Walk.segment,PortGraph.Walk.reverse,Nat.zero_add,Fin.val_castSucc]
omit [Fintype D] [Fintype A] [DecidableEq A] [Fintype V] [Nonempty V] [Nonempty D] in
lemma path_literal (cap : ℕ) (p : G.Walk cap) (n : Fin (cap+1)) (b c : Advice D A cap) :
    C.PathAccept n.val (p.segment 0 n.val (by omega)) b c ↔
      Test cap n p.port (fun k => G.back (p.vertex k.castSucc) (p.port k))
        (fun k => C.allowed (p.vertex k.castSucc,p.port k)) b c := by
  unfold PortCSP.PathAccept Test
  apply forall_congr'
  intro i
  apply forall_congr'
  intro j
  apply forall_congr'
  intro h
  have he : (p.segment 0 n.val (by omega)).cast h=p.segment 0 (i.val+(j.val+1)) (by omega) := by
    have cast_segment (n m : ℕ) (hn : 0+n≤cap) (h : n=m) :
        (p.segment 0 n hn).cast h=p.segment 0 m (by omega) := by
      subst m
      rfl
    exact cast_segment _ _ _ h
  rw [he]
  exact cut_prefix C cap i.val j.val (by omega) p b c
omit [DecidableEq A] [Fintype V] [Nonempty V] [Nonempty D] in
lemma relation_correct (cap : ℕ) (p : G.Walk cap) (n : Fin (cap+1)) :
    relation cap n p.port (fun k => G.back (p.vertex k.castSucc) (p.port k))
      (fun k => C.allowed (p.vertex k.castSucc,p.port k)) =
    Finset.univ.filter (fun bc : Advice D A cap × Advice D A cap =>
      C.PathAccept n.val (p.segment 0 n.val (by omega)) bc.1 bc.2) := by
  apply Finset.ext
  intro bc
  simp only [relation,Finset.mem_filter,Finset.mem_univ,true_and]
  exact (path_literal C cap p n bc.1 bc.2).symm
end MetricKMedian.PCP.Compiler.PowerProgram

end Inline_PCPPathTable

end OAI
