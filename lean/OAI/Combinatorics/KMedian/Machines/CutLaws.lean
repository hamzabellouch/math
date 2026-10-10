import Mathlib
import OAI.Combinatorics.KMedian.Amplification.PoweringConstruction

namespace OAI

section Inline_PCPCutLaws
namespace MetricKMedian.PCP.PortGraph.Walk
variable {V D : Type} {G : PortGraph V D}
lemma center_left_walk (i j : ℕ) (p : G.Walk (i+(j+1))) :
    ofWord (G := G) (centerEquiv i j p).1.1 (centerEquiv i j p).1.2=
      (p.segment 0 i (by omega)).reverse := by
  change wordEquiv.symm (wordEquiv ((p.segment 0 i (by omega)).reverse))=_
  exact wordEquiv.symm_apply_apply _
lemma center_right_word (i j : ℕ) (p : G.Walk (i+(j+1))) :
    (centerEquiv i j p).2.2=(p.segment (i+1) j (by omega)).port := by
  funext k
  simp only [centerEquiv,Equiv.trans_apply,Equiv.prodCongr_apply,splitEquiv,Fin.consEquiv,
    segment,Equiv.coe_fn_mk]
  change p.port ⟨i+(k.val+1),_⟩=p.port ⟨i+1+k.val,_⟩
  congr 1
  apply Fin.ext
  change i+(k.val+1)=i+1+k.val
  omega
lemma center_right_walk (i j : ℕ) (p : G.Walk (i+(j+1))) :
    ofWord (G := G) (G.step (centerEquiv i j p).1.1 (centerEquiv i j p).2.1)
      (centerEquiv i j p).2.2=p.segment (i+1) j (by omega) := by
  rw [center_vertex,center_port,center_right_word]
  have hc : G.step (p.vertex ⟨i,by omega⟩) (p.port ⟨i,by omega⟩)=p.vertex ⟨i+1,by omega⟩ := p.chain ⟨i,by omega⟩
  rw [hc]
  change wordEquiv.symm (wordEquiv (p.segment (i+1) j (by omega)))=_
  exact wordEquiv.symm_apply_apply _
end MetricKMedian.PCP.PortGraph.Walk
namespace MetricKMedian.PCP.PortCSP
variable {V D A : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
  [Fintype A] [Inhabited A] [DecidableEq A] {G : PortGraph V D} (C : PortCSP G A) {cap : ℕ}
open PortGraph

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D] [Fintype A] [DecidableEq A] in
lemma cut_literal (i j : ℕ) (p : G.Walk (i+(j+1))) (b c : Advice D A cap) :
    C.CutAccept i j p b c ↔
    (b.get i (p.segment 0 i (by omega)).port,
     c.get j (p.segment (i+1) j (by omega)).reverse.port) ∈
      C.allowed (p.vertex ⟨i,by omega⟩,p.port ⟨i,by omega⟩) := by
  unfold CutAccept
  dsimp only
  rw [Walk.center_left_walk,Walk.reverse_reverse,Walk.center_right_walk,
    Walk.center_vertex,Walk.center_port]
end MetricKMedian.PCP.PortCSP

end Inline_PCPCutLaws

end OAI
