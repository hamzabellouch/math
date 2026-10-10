import Mathlib
import OAI.Probability.SKGap.Matrix.WordFockSeries

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.Tensor.Series
open Diagram InverseDiagram WordSeries Loop
variable {ι : Type*} [Fintype ι]
namespace GradedWords

def branch (j : ℝ) (p : ι→ℝ) (U V : GradedWords ι×GradedWords ι) : GradedWords ι×GradedWords ι :=
  (prepend (.diag p) U.2++V.1,
    (bump (prepend .noise (prepend (.diag p) U.2))++
      scale (-(j*Diagram.mean p)) (bump (bump U.1)))++V.2)
def ordinaryWords (j : ℝ) : SourceTree (ι→ℝ)→GradedWords ι×GradedWords ι
  | .leaf c => (scalar c,bump (prepend .noise (scalar c)))
  | .branch p t u => branch j p (ordinaryWords j t) (ordinaryWords j u)
def implicitSource (j : ℝ) (a p : ι→ℝ) (t : SourceTree (ι→ℝ)) : GradedWords ι :=
  prepend .inverse (prepend (.diag p) (ordinaryWords j t).2++
    scale (-(j*Diagram.mean p)) (bump (bump (prepend (.diag a) (ordinaryWords j t).1))))
def implicitField (j : ℝ) (a p : ι→ℝ) (t : SourceTree (ι→ℝ)) : GradedWords ι :=
  (bump (prepend .noise (implicitSource j a p t))++
    scale (-(j*Diagram.mean a)) (bump (bump (implicitSource j a p t))))++
    scale (-(j*Diagram.mean p)) (bump (bump (ordinaryWords j t).1))

def pairSeq (j : ℝ) (a : ι→ℝ) (P : GradedWords ι×GradedWords ι) :=
  (seq j a P.1,seq j a P.2)
lemma pairSeq_branch (j : ℝ) (a p : ι→ℝ) (U V : GradedWords ι×GradedWords ι) :
    pairSeq j a (branch j p U V)=
      (branchSource p (pairSeq j a U) (pairSeq j a V),
       branchField j p (pairSeq j a U) (pairSeq j a V)) := by
  simp [pairSeq,branch,branchSource,branchField,seq_append,seq_bump,seq_prepend,
    seq_scale,letterOperator,sub_eq_add_neg,add_assoc]
lemma pairSeq_ordinary (j : ℝ) (a : ι→ℝ) (t : SourceTree (ι→ℝ)) :
    pairSeq j a (ordinaryWords j t)=ordinary j t := by
  induction t with
  | leaf c =>
    simp [ordinaryWords,pairSeq,seq_scalar,seq_bump,seq_prepend,letterOperator,
      ordinary,act_ofVector]
  | branch p t u ih1 ih2 => simp only [ordinaryWords,pairSeq_branch,ih1,ih2,ordinary]
lemma seq_implicitSource (j : ℝ) (a p : ι→ℝ) (t : SourceTree (ι→ℝ)) :
    seq j a (implicitSource j a p t)=loopSource j a p t := by
  have h1:=congrArg Prod.fst (pairSeq_ordinary j a t)
  have h2:=congrArg Prod.snd (pairSeq_ordinary j a t)
  simp only [pairSeq] at h1 h2
  simp [implicitSource,seq_prepend,seq_append,seq_scale,seq_bump,letterOperator,
    h1,h2,loopSource,sub_eq_add_neg]
lemma seq_implicitField (j : ℝ) (a p : ι→ℝ) (t : SourceTree (ι→ℝ)) :
    seq j a (implicitField j a p t)=loopField j a p t := by
  have h1:=congrArg Prod.fst (pairSeq_ordinary j a t)
  simp only [pairSeq] at h1
  simp [implicitField,seq_prepend,seq_append,seq_scale,seq_bump,letterOperator,
    h1,seq_implicitSource,loopField,sub_eq_add_neg,add_assoc]

section
omit [Fintype ι]

def bounded (k : ℕ) (P : GradedWords ι) : Prop := ∀ t∈P,inverseCount t.2.2≤k
lemma bounded_mono {k l : ℕ} (hkl : k≤l) {P : GradedWords ι} (h : bounded k P) : bounded l P :=
  fun t ht=>(h t ht).trans hkl
lemma bounded_scalar (k : ℕ) (c : ℝ) : bounded k (scalar (ι:=ι) c) := by
  rintro t ht
  simp only [scalar,List.mem_singleton] at ht
  subst t
  simp [inverseCount]
lemma bounded_append {k : ℕ} {P Q : GradedWords ι} (hP : bounded k P) (hQ : bounded k Q) :
    bounded k (P++Q) := by
  intro t ht
  rcases List.mem_append.mp ht with h|h
  · exact hP t h
  · exact hQ t h
lemma bounded_scale {k : ℕ} {P : GradedWords ι} (c : ℝ) (hP : bounded k P) : bounded k (scale c P) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
  exact hP s hs
lemma bounded_bump {k : ℕ} {P : GradedWords ι} (hP : bounded k P) : bounded k (bump P) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
  exact hP s hs
lemma bounded_diag {k : ℕ} {P : GradedWords ι} (d : ι→ℝ) (hP : bounded k P) :
    bounded k (prepend (.diag d) P) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
  exact hP s hs
lemma bounded_noise {k : ℕ} {P : GradedWords ι} (hP : bounded k P) :
    bounded k (prepend .noise P) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
  exact hP s hs
lemma bounded_inverse {k : ℕ} {P : GradedWords ι} (hP : bounded k P) :
    bounded (k+1) (prepend .inverse P) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
  simpa only [inverseCount_inverse] using Nat.add_le_add_right (hP s hs) 1

end

lemma bounded_branch {k : ℕ} (j : ℝ) (p : ι→ℝ) {U V : GradedWords ι×GradedWords ι}
    (hU : bounded k U.1 ∧ bounded k U.2) (hV : bounded k V.1 ∧ bounded k V.2) :
    bounded k (branch j p U V).1 ∧ bounded k (branch j p U V).2 := by
  exact ⟨bounded_append (bounded_diag _ hU.2) hV.1,
    bounded_append (bounded_append (bounded_bump (bounded_noise (bounded_diag _ hU.2)))
      (bounded_scale _ (bounded_bump (bounded_bump hU.1)))) hV.2⟩
lemma bounded_ordinary (j : ℝ) (t : SourceTree (ι→ℝ)) :
    bounded 0 (ordinaryWords j t).1 ∧ bounded 0 (ordinaryWords j t).2 := by
  induction t with
  | leaf c => exact ⟨bounded_scalar 0 c,bounded_bump (bounded_noise (bounded_scalar 0 c))⟩
  | branch p t u ih1 ih2 => exact bounded_branch j p ih1 ih2
lemma bounded_implicitSource (j : ℝ) (a p : ι→ℝ) (t : SourceTree (ι→ℝ)) :
    bounded 1 (implicitSource j a p t) := by
  have h:=bounded_ordinary j t
  exact bounded_inverse (bounded_append (bounded_diag _ h.2)
    (bounded_scale _ (bounded_bump (bounded_bump (bounded_diag _ h.1)))))
lemma bounded_implicitField (j : ℝ) (a p : ι→ℝ) (t : SourceTree (ι→ℝ)) :
    bounded 1 (implicitField j a p t) := by
  have h:=bounded_implicitSource j a p t
  exact bounded_append (bounded_append (bounded_bump (bounded_noise h))
    (bounded_scale _ (bounded_bump (bounded_bump h))))
    (bounded_scale _ (bounded_bump (bounded_bump (bounded_mono (by omega) (bounded_ordinary j t).1))))
end GradedWords

namespace ClosedTree
open GradedWords

def words (j : ℝ) (a : ι→ℝ) : ClosedTree (ι→ℝ)→GradedWords ι×GradedWords ι
  | .leaf c => ordinaryWords j (.leaf c)
  | .implicit p t => (implicitSource j a p t,implicitField j a p t)
  | .branch p t u => GradedWords.branch j p (t.words j a) (u.words j a)
lemma words_series (j : ℝ) (a : ι→ℝ) (t : ClosedTree (ι→ℝ)) :
    pairSeq j a (t.words j a)=t.series j a := by
  induction t with
  | leaf c => exact pairSeq_ordinary j a (.leaf c)
  | implicit p t => exact Prod.ext (seq_implicitSource j a p t) (seq_implicitField j a p t)
  | branch p t u ih1 ih2 => simp only [words,pairSeq_branch,ih1,ih2,series]
lemma words_bounded (j : ℝ) (a : ι→ℝ) (t : ClosedTree (ι→ℝ)) :
    bounded 1 (t.words j a).1 ∧ bounded 1 (t.words j a).2 := by
  induction t with
  | leaf c =>
    exact ⟨bounded_mono (by omega) (bounded_ordinary j (.leaf c)).1,
      bounded_mono (by omega) (bounded_ordinary j (.leaf c)).2⟩
  | implicit p t => exact ⟨bounded_implicitSource j a p t,bounded_implicitField j a p t⟩
  | branch p t u ih1 ih2 => exact bounded_branch j p ih1 ih2

theorem field_prediction_zero (j : ℝ) (a : ι→ℝ) (t : ClosedTree (ι→ℝ)) (z : ℝ) (i : ι) :
    prediction j a z (t.words j a).2 i=0 := by
  apply prediction_zero_of_project j a _ (t.words_bounded j a).2
  intro n
  have h:=congrArg Prod.snd (t.words_series j a)
  change seq j a (t.words j a).2=(t.series j a).2 at h
  rw [h]
  exact t.project_field j a n ▸ rfl

theorem source_prediction_zero (j : ℝ) (a : ι→ℝ) (t : ClosedTree (ι→ℝ))
    (ht : t.leafMass=0) (z : ℝ) (i : ι) : prediction j a z (t.words j a).1 i=0 := by
  apply prediction_zero_of_project j a _ (t.words_bounded j a).1
  intro n
  have h:=congrArg Prod.fst (t.words_series j a)
  change seq j a (t.words j a).1=(t.series j a).1 at h
  rw [h,t.project_source,ht]
  split_ifs <;> rfl
end ClosedTree
end SKGap.Noncrossing.Primary.Tensor.Series

end
end

end OAI
