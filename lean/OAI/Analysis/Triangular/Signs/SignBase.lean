import OAI.Analysis.Triangular.Taylor.TaylorRowsBase

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

def ordinaryOffset (n : Fin 7) (r : Fin 8) : ℝ :=
  if n.val=0 ∧ r.val=1 then Q 1/(2*Z)
  else if n.val=1 ∧ r.val=3 then (4/5:ℝ)*Q 1 else 0
def ordinarySignRow (side : Fin 2) (n : Fin 7) (y : Fin 2) (l : Fin 21) (r : Fin 8) : ℝ :=
  if side.val=0 then (if l.val=0 then ordinaryOffset n r else 0) -
    taylorRow side (nearNode n) (nearDisplacement n y) l.val r
  else taylorRow side (nearNode n) (nearDisplacement n y) l.val r
def ordinarySignValue (side : Fin 2) (n : Fin 7) (y : Fin 2) (e : Fin 8 → ℝ) (τ : ℝ) : ℝ :=
  if side.val=0 then (∑ r : Fin 8, ordinaryOffset n r*e r) -
    finiteTaylor side (nearNode n) (nearDisplacement n y) e τ
  else finiteTaylor side (nearNode n) (nearDisplacement n y) e τ
lemma ordinarySignValue_eq (side : Fin 2) (n : Fin 7) (y : Fin 2) (e : Fin 8 → ℝ) (τ : ℝ) :
    ordinarySignValue side n y e τ =
      ∑ l : Fin 21, (∑ r : Fin 8, ordinarySignRow side n y l r*e r)*τ^l.val := by
  have ht : (∑ l : Fin 21, (∑ r : Fin 8,
      taylorRow side (nearNode n) (nearDisplacement n y) l.val r*e r)*τ^l.val) =
      finiteTaylor side (nearNode n) (nearDisplacement n y) e τ := by
    rw [finiteTaylor,← Fin.sum_univ_eq_sum_range]
  unfold ordinarySignValue ordinarySignRow
  split_ifs with h
  · simp only [sub_mul,Finset.sum_sub_distrib,ite_mul,zero_mul,
      Finset.sum_ite_irrel,ht,Finset.sum_const_zero]
    congr 1
    symm
    rw [Finset.sum_eq_single (0:Fin 21)]
    · simp
    · intro b hb hb0
      have hne : b.val ≠ 0 := by intro hh; apply hb0; exact Fin.ext hh
      simp [hne]
    · simp
  · exact ht.symm
end AtomicTriangular.Construction
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def ordinaryOffsetBox (n : Fin 7) (r : Fin 8) : RI :=
  if n.val=0 ∧ r.val=1 then QBox1.mul ((RI.point 2).mul ZBox).invPos
  else if n.val=1 ∧ r.val=3 then ((RI.point 4).divNat 5).mul QBox1 else RI.point 0
lemma ordinaryOffsetBox_mem (n : Fin 7) (r : Fin 8) :
    (ordinaryOffsetBox n r).Mem (ordinaryOffset n r) := by
  unfold ordinaryOffsetBox ordinaryOffset
  split_ifs
  · rw [div_eq_mul_inv]
    exact RI.mem_mul QBox1_mem (RI.mem_invPos (RI.mem_mul (RI.mem_point 2) ZBox_mem) (by decide +kernel))
  · exact RI.mem_mul (RI.mem_divNat (RI.mem_point 4) (by norm_num)) QBox1_mem
  · simpa using RI.mem_point 0

def ordinarySignRowBox (side : Fin 2) (n : Fin 7) (a : Fin 21 → Fin 8 → RI)
    (l : Fin 21) (r : Fin 8) : RI :=
  if side.val=0 then ((if l.val=0 then ordinaryOffsetBox n r else RI.point 0).sub (a l r)) else a l r
lemma ordinarySignRowBox_mem (side : Fin 2) (n : Fin 7) (y : Fin 2)
    {a : Fin 21 → Fin 8 → RI}
    (ha : ∀ l r, (a l r).Mem (taylorRow side (nearNode n) (nearDisplacement n y) l.val r))
    (l : Fin 21) (r : Fin 8) :
    (ordinarySignRowBox side n a l r).Mem (ordinarySignRow side n y l r) := by
  unfold ordinarySignRowBox ordinarySignRow
  split_ifs
  · exact RI.mem_sub (ordinaryOffsetBox_mem n r) (ha l r)
  · exact RI.mem_sub (by simpa using RI.mem_point 0) (ha l r)
  · exact ha l r
end AtomicTriangular.FiniteCertificate
end

end OAI
