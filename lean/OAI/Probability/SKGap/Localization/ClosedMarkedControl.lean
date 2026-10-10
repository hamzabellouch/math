import Mathlib
import OAI.Probability.SKGap.Localization.MarkedDiagnostic
import OAI.Probability.SKGap.Matrix.ClosedErrorTrace
import OAI.Probability.SKGap.Localization.StartedMarked

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.ClosedMarked
open SKGapCutoff.Recipe Primary Primary.Tensor.Series Marked
variable {n : ℕ}
lemma closedWordBounded_diag {A : ℝ} {w : Word n} (hw : closedWordBounded A w) (d : Fin n→ℝ) (hd : ∀i,|d i|≤A) :
    closedWordBounded A (w++[.diag d]) := by
  apply closedWordBounded_append hw
  intro l hl;have he:=List.mem_singleton.mp hl;subst l;exact hd

def MarkControl (A : ℝ) (L : ℕ) (t : Mark n) : Prop :=
  ∀d:Fin n→ℝ,(∀i,|d i|≤1)→ closedWordBounded A (t.diagnostic d) ∧ (t.diagnostic d).length≤L

def MarkedControl (A : ℝ) (L : ℕ) (P : Marked n) : Prop := ∀t∈P,MarkControl A L t.2

def PairControl (A : ℝ) (L : ℕ) (P : Pair n) : Prop := MarkedControl A L P.1 ∧ MarkedControl A L P.2

lemma MarkControl.mono {A : ℝ} {L K : ℕ} {t : Mark n} (h : MarkControl A L t) (hLK : L≤K) :
    MarkControl A K t := fun d hd=>⟨(h d hd).1,(h d hd).2.trans hLK⟩

lemma MarkControl.prepend {A : ℝ} {L : ℕ} {t : Mark n} (h : MarkControl A L t)
    (P : Word n) (hp : closedWordBounded A P) : MarkControl A (L+P.length) (t.prepend P) := by
  intro d hd
  rcases h d hd with ⟨hb,hl⟩
  cases t with
  | diagonal Q s R=>
    simp only [Mark.prepend,Mark.diagnostic,List.length_append,List.length_cons] at *
    constructor
    · intro l hh
      simp only [List.mem_append,List.mem_cons] at hh
      rcases hh with hh|hh|hh|hh
      · exact hb l (List.mem_append_left _ hh)
      · subst l; exact hb (.diag d) (by simp)
      · exact hp l hh
      · exact hb l (by simp [hh])
    · omega
  | average s Q=>
    simp only [Mark.prepend,Mark.diagnostic] at *
    exact ⟨closedWordBounded_append hp hb,by simp only [List.length_append]; omega⟩

lemma MarkedControl.append {A : ℝ} {L : ℕ} {P Q : Marked n}
    (hp : MarkedControl A L P) (hq : MarkedControl A L Q) : MarkedControl A L (P++Q) := by
  intro t ht; rcases List.mem_append.mp ht with ht|ht
  · exact hp t ht
  · exact hq t ht

lemma MarkedControl.mono {A : ℝ} {L K : ℕ} {P : Marked n}
    (h : MarkedControl A L P) (hLK : L≤K) : MarkedControl A K P := fun t ht=>(h t ht).mono hLK

lemma MarkedControl.prepend {A : ℝ} {L : ℕ} {P : Marked n}
    (h : MarkedControl A L P) (w : Word n) (hw : closedWordBounded A w) :
    MarkedControl A (L+w.length) (P.prepend w) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
  exact (h s hs).prepend w hw

lemma MarkedControl.scale {A : ℝ} {L : ℕ} {P : Marked n}
    (h : MarkedControl A L P) (c : ℝ) : MarkedControl A L (P.scale c) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
  exact h s hs

lemma diagonalWords_control {A : ℝ} {L : ℕ} (hA : 1≤A) (s : Fin n→ℝ)
    (P : GradedWords (Fin n)) (hP : ∀t∈P,closedWordBounded A t.2.2 ∧ t.2.2.length≤L) :
    MarkedControl A (L+1) (diagonalWords s P) := by
  intro t ht d hd
  obtain ⟨r,hr,he⟩:=List.mem_map.mp ht
  subst t
  simp only [Mark.diagnostic,List.length_append,List.length_cons,List.length_nil]
  exact ⟨closedWordBounded_diag (hP r hr).1 d (fun i=>(hd i).trans hA),by have hh:=(hP r hr).2; omega⟩

lemma averageWords_control {A : ℝ} {L : ℕ} (c : ℝ) (s : Fin n→ℝ)
    (P : GradedWords (Fin n)) (hP : ∀t∈P,closedWordBounded A t.2.2 ∧ t.2.2.length≤L) :
    MarkedControl A L (averageWords c s P) := by
  intro t ht d hd
  obtain ⟨r,hr,he⟩:=List.mem_map.mp ht
  subst t
  exact hP r hr

lemma zeroPair_control {A : ℝ} {L : ℕ} (hL : 1≤L) : PairControl (n:=n) A L zeroPair := by
  constructor
  · intro t ht; have he:=List.mem_singleton.mp ht; subst t
    intro d hd; exact ⟨by intro l hl; simp [Mark.diagnostic] at hl,by simp [Mark.diagnostic]⟩
  · intro t ht; have he:=List.mem_singleton.mp ht; subst t
    intro d hd
    constructor
    · intro l hl
      have he : l=WordLetter.noise := by simpa [Mark.diagnostic] using hl
      subst l
      trivial
    · simpa [Mark.diagnostic] using hL

lemma smallBranch_control {A : ℝ} {L K : ℕ} (hA : 1≤A) (hLK : L+2≤K)
    (j : ℝ) (p : Fin n→ℝ) (T : GradedWords (Fin n)×GradedWords (Fin n)) (V : Pair n)
    (hT : (∀t∈T.1,closedWordBounded A t.2.2 ∧ t.2.2.length≤L) ∧
      (∀t∈T.2,closedWordBounded A t.2.2 ∧ t.2.2.length≤L))
    (hV : PairControl A K V) : PairControl A K (smallBranch j p T V) := by
  have hd:=diagonalWords_control hA p _ hT.2
  have ha:=averageWords_control (-j) p _ hT.1
  have hn : closedWordBounded (n:=n) A [.noise] := by intro l hl; have he:=List.mem_singleton.mp hl; subst l; trivial
  refine ⟨(hd.mono (by omega)).append hV.1,?_⟩
  exact (((hd.prepend [.noise] hn).mono (by simp only [List.length_cons,List.length_nil]; omega)).append (ha.mono (by omega))).append hV.2

lemma boundedBranch_control {A : ℝ} {L K : ℕ} (hLK : L+2≤K)
    (j : ℝ) (p : Fin n→ℝ) (hp : ∀i,|p i|≤A) (U V : Pair n)
    (hU : PairControl A L U) (hV : PairControl A K V) : PairControl A K (boundedBranch j p U V) := by
  have hd : closedWordBounded (n:=n) A [.diag p] := by intro l hl; have he:=List.mem_singleton.mp hl; subst l; exact hp
  have hd' : closedWordBounded (n:=n) A [.noise,.diag p] := by
    intro l hl; simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
    rcases hl with rfl|rfl
    · trivial
    · exact hp
  refine ⟨((hU.2.prepend [.diag p] hd).mono (by simp only [List.length_singleton]; omega)).append hV.1,?_⟩
  exact (((hU.2.prepend [.noise,.diag p] hd').mono (by simp only [List.length_cons,List.length_nil]; omega)).append
    ((hU.1.scale _).mono (by omega))).append hV.2

end SKGap.Noncrossing.ClosedMarked

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.ClosedMarked
open SKGapCutoff.Recipe Primary Primary.Tensor.Series Marked
variable {n : ℕ}

def GradedControl (A : ℝ) (L : ℕ) (P : GradedWords (Fin n)) : Prop :=
  ∀v∈P,closedWordBounded A v.2.2 ∧ v.2.2.length≤L

lemma PairControl.mono {A : ℝ} {L K : ℕ} {P : Pair n} (h : PairControl A L P) (hLK : L≤K) :
    PairControl A K P := ⟨h.1.mono hLK,h.2.mono hLK⟩
lemma implicitPair_control (j : ℝ) (a p : Fin n→ℝ) (T : SourceTree (Fin n→ℝ))
    {A : ℝ} {L : ℕ} (hA : 1≤A) (ha : ∀i,|a i|≤A)
    (hT : GradedControl A L (GradedWords.ordinaryWords j T).1 ∧
      GradedControl A L (GradedWords.ordinaryWords j T).2) :
    PairControl A (L+3) (implicitPair j a p T) := by
  have hd:=diagonalWords_control hA p _ hT.2
  have hm:=averageWords_control (-j) p _ hT.1
  have hb : closedWordBounded (n:=n) A [.inverse] := by
    intro l hl;have he:=List.mem_singleton.mp hl;subst l;trivial
  have hba : closedWordBounded A [.inverse,.diag a] := by
    intro l hl;simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
    rcases hl with rfl|rfl
    · trivial
    · exact ha
  have hS : MarkedControl A (L+2) (implicitPair j a p T).1 := by
    exact ((hd.prepend [.inverse] hb).mono (by simp)).append
      ((hm.prepend [.inverse,.diag a] hba).mono (by simp))
  have hn : closedWordBounded (n:=n) A [.noise] := by
    intro l hl;have he:=List.mem_singleton.mp hl;subst l;trivial
  refine ⟨hS.mono (by omega),?_⟩
  exact (((hS.prepend [.noise] hn).mono (by simp)).append
    ((hS.scale _).mono (by omega))).append (hm.mono (by omega))

namespace SmallTree
lemma smallBranches_control (j : ℝ) (a₀ : Fin n→ℝ) {A : ℝ} {L K : ℕ}
    (hA : 1≤A) (hLK : L+2≤K)
    (xs : List ((Fin n→ℝ)×ClosedTree (Fin n→ℝ))) (U : SmallTree n)
    (hT : ∀t∈xs,GradedControl A L (t.2.words j a₀).1 ∧ GradedControl A L (t.2.words j a₀).2)
    (hU : PairControl A K (U.marked j a₀)) :
    PairControl A K ((smallBranches xs U).marked j a₀) := by
  induction xs with
  | nil=>exact hU
  | cons t xs ih=>
    exact smallBranch_control hA hLK j _ _ _ (hT t (by simp)) (ih (fun v hv=>hT v (by simp [hv])))
lemma boundedBranches_control (j : ℝ) (a₀ : Fin n→ℝ) {A : ℝ} {L K : ℕ}
    (hLK : L+2≤K)
    (xs : List ((Fin n→ℝ)×SmallTree n)) (U : SmallTree n)
    (ha : ∀t∈xs,∀i,|t.1 i|≤A) (hT : ∀t∈xs,PairControl A L (t.2.marked j a₀))
    (hU : PairControl A K (U.marked j a₀)) :
    PairControl A K ((boundedBranches xs U).marked j a₀) := by
  induction xs with
  | nil=>exact hU
  | cons t xs ih=>
    exact boundedBranch_control hLK j _ (ha t (by simp)) _ _ (hT t (by simp))
      (ih (fun v hv=>ha v (by simp [hv])) (fun v hv=>hT v (by simp [hv])))
end SmallTree
end SKGap.Noncrossing.ClosedMarked
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series
open SKGap.Noncrossing.ClosedMarked
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
variable (D : OrdinaryData n ι κ σ)

theorem startedMarked_control (w y : VectorFields n) (T : ι→SourceTree (Fin n→ℝ))
    (t₀ : SmallTree n) (a₀ : Fin n→ℝ) (x : Spin n) (N L : ℕ) {A : ℝ} (hA : 1≤A)
    (hinit : SKGap.Noncrossing.ClosedMarked.PairControl A (L+3) (t₀.marked D.j a₀))
    (hT : ∀l,GradedControl A L (GradedWords.ordinaryWords D.j (T l)).1 ∧
      GradedControl A L (GradedWords.ordinaryWords D.j (T l)).2)
    (ha : ∀a≤N,∀b i,|D.auxCoefficient a b x i|≤A) :
    ∀a≤N,SKGap.Noncrossing.ClosedMarked.PairControl A (L+2*a+3) ((D.startedSmallTree w y T t₀ x a).marked D.j a₀) := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih=>
    intro haN
    rcases a with _|r
    · simpa only [startedSmallTree,Nat.mul_zero,Nat.add_zero] using hinit
    · rw [startedSmallTree]
      apply SmallTree.smallBranches_control D.j a₀ (L:=L) hA (by omega)
      · intro t ht
        obtain ⟨l,hl,rfl⟩:=List.mem_map.mp ht
        simpa only [ClosedTree.words_ofOrdinary] using hT l
      · apply SmallTree.boundedBranches_control D.j a₀ (L:=L+2*r+3) (by omega)
        · intro t ht;obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ht
          exact ha (r+1) haN b
        · intro t ht;obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ht
          exact (ih b b.isLt (b.isLt.le.trans haN)).mono (by omega)
        · exact SKGap.Noncrossing.ClosedMarked.zeroPair_control (by omega)
end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
