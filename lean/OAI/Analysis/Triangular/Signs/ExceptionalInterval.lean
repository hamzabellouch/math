import OAI.Analysis.Triangular.Taylor.TaylorRows00
import OAI.Analysis.Triangular.Signs.Exceptional

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma exceptional_tr_mem (l : Fin 21) (r : Fin 8) :
    (tr0_0_1 l r).Mem (taylorRow 0 1 1 l.val r) := by
  have hh := tr0_0_1_mem l r
  have hn : nearNode 0 = 1 := by norm_num [nearNode, finiteNode, residue]
  have hy : nearDisplacement 0 1 = 1 := by norm_num [nearDisplacement,nearDisplacementNum]
  simpa only [hn,hy] using hh
lemma ep0 : (RI.point 0).Mem (0 : ℝ) := by simpa using RI.mem_point 0
lemma ep1 : (RI.point 1).Mem (1 : ℝ) := by simpa using RI.mem_point 1
lemma ep2 : (RI.point 2).Mem (2 : ℝ) := by simpa using RI.mem_point 2
lemma ep4 : (RI.point 4).Mem (4 : ℝ) := by simpa using RI.mem_point 4
lemma ep6 : (RI.point 6).Mem (6 : ℝ) := by simpa using RI.mem_point 6

def frozenTaylorRowBox (z : RI) (l : Fin 21) (r : Fin 8) : RI :=
  (if r.val=0 then RI.point 0 else (tr0_0_1 l r).neg).sub
    (if r.val=1 then z.mul (tr0_0_1 l 0) else RI.point 0)
lemma frozenTaylorRowBox_mem {z : RI} {x : ℝ} (hz : z.Mem x) (l : Fin 21) (r : Fin 8) :
    (frozenTaylorRowBox z l r).Mem (frozenTaylorRow x l.val r) := by
  unfold frozenTaylorRowBox frozenTaylorRow
  apply RI.mem_sub
  · split_ifs
    · exact ep0
    · exact RI.mem_neg (exceptional_tr_mem l r)
  · split_ifs
    · exact RI.mem_mul hz (exceptional_tr_mem l 0)
    · exact ep0

def exceptionalWeightBox (test : Fin 4) (endpt : Fin 2) (j : Fin 3) : RI :=
  if test.val=0 then (if endpt.val=0 ∧ j.val=1 then RI.point 1 else RI.point 0)
  else if test.val=1 then (if endpt.val=0 then
    (if j.val=1 then ((RI.point 4).mul ZBox).divNat 3 else if j.val=2 then (RI.point 2).divNat 3 else RI.point 0)
    else if j.val=2 then (RI.point 1).divNat 3 else RI.point 0)
  else if test.val=2 then (if endpt.val=0 then
    (if j.val=0 then (RI.point 2).mul (ZBox.pow 2) else if j.val=1 then ((RI.point 4).mul ZBox).divNat 3 else (RI.point 1).divNat 3)
    else (if j.val=1 then ((RI.point 4).mul ZBox).divNat 3 else if j.val=2 then (RI.point 2).divNat 3 else RI.point 0))
  else (if endpt.val=1 then (if j.val=0 then (RI.point 6).mul (ZBox.pow 2) else if j.val=1 then (RI.point 4).mul ZBox else RI.point 1) else RI.point 0)
lemma exceptionalWeightBox_mem (test : Fin 4) (ep : Fin 2) (j : Fin 3) :
    (exceptionalWeightBox test ep j).Mem (exceptionalWeight test ep j) := by
  unfold exceptionalWeightBox exceptionalWeight
  split_ifs
  all_goals first
    | exact ep0
    | exact ep1
    | exact RI.mem_divNat ep1 (by norm_num)
    | exact RI.mem_divNat ep2 (by norm_num)
    | exact RI.mem_divNat (RI.mem_mul ep4 ZBox_mem) (by norm_num)
    | exact RI.mem_mul ep2 (RI.mem_pow ZBox_mem 2)
    | exact RI.mem_mul ep6 (RI.mem_pow ZBox_mem 2)
    | exact RI.mem_mul ep4 ZBox_mem

def exceptionalOffsetBox (test : Fin 4) (l : ℕ) (r : Fin 8) : RI :=
  if r.val=1 then (if l=0 then QBox1.mul (if test.val=0 then RI.point 1 else (RI.point test.val).mul ZBox)
    else if l=1 ∧ test.val≠0 then QBox1 else RI.point 0) else RI.point 0
lemma exceptionalOffsetBox_mem (test : Fin 4) (l : ℕ) (r : Fin 8) :
    (exceptionalOffsetBox test l r).Mem (exceptionalOffset test l r) := by
  unfold exceptionalOffsetBox exceptionalOffset
  split_ifs
  · exact RI.mem_mul QBox1_mem ep1
  · exact RI.mem_mul QBox1_mem (RI.mem_mul (by simpa using RI.mem_point (test.val:ℤ)) ZBox_mem)
  · exact QBox1_mem
  · exact ep0
  · exact ep0

def exceptionalRowBox (test : Fin 4) (l : Fin 23) (r : Fin 8) : RI :=
  (exceptionalOffsetBox test l.val r).add (RI.sum (fun ep : Fin 2 => RI.sum (fun j : Fin 3 =>
    if h : j.val≤l.val ∧ l.val-j.val<21 then
      (exceptionalWeightBox test ep j).mul (frozenTaylorRowBox (if ep.val=0 then RI.point 0 else ZBox) ⟨l.val-j.val,h.2⟩ r) else RI.point 0)))
lemma exceptionalRowBox_mem (test : Fin 4) (l : Fin 23) (r : Fin 8) :
    (exceptionalRowBox test l r).Mem (exceptionalRow test l r) := by
  unfold exceptionalRowBox exceptionalRow
  apply RI.mem_add (exceptionalOffsetBox_mem test l.val r)
  apply RI.mem_sum
  intro ep
  apply RI.mem_sum
  intro j
  split
  · apply RI.mem_mul (exceptionalWeightBox_mem test ep j)
    apply frozenTaylorRowBox_mem
    split_ifs
    · exact ep0
    · exact ZBox_mem
  · exact ep0
end AtomicTriangular.FiniteCertificate
end

end OAI
