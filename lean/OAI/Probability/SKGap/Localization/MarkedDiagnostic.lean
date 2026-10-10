import Mathlib
import OAI.Probability.SKGap.Matrix.PrimitiveTrace
import OAI.Probability.SKGap.Localization.RecipeMarked

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.MarkedPolynomial
variable {n : ℕ}
lemma wordBounded_append {A : ℝ} {u v : OrdinaryWord n}
    (hu : wordBounded A u) (hv : wordBounded A v) : wordBounded A (u++v) := by
  intro l hl; rcases List.mem_append.mp hl with hl|hl
  · exact hu l hl
  · exact hv l hl

lemma wordBounded_mono {A B : ℝ} {u : OrdinaryWord n} (h : wordBounded A u) (hab : A≤B) :
    wordBounded B u := by
  intro l hl; cases l with
  | noise=>trivial
  | diag p=>exact fun i=>(h (.diag p) hl i).trans hab

def MarkControl (A : ℝ) (L : ℕ) (t : SmallMark n) : Prop :=
  ∀d:Fin n→ℝ,(∀i,|d i|≤1)→ wordBounded A (t.diagnostic d) ∧ (t.diagnostic d).length≤L

def MarkedControl (A : ℝ) (L : ℕ) (P : MarkedPolynomial n) : Prop := ∀t∈P,MarkControl A L t.2

def PairControl (A : ℝ) (L : ℕ) (P : Pair n) : Prop := MarkedControl A L P.1 ∧ MarkedControl A L P.2

lemma MarkControl.mono {A : ℝ} {L K : ℕ} {t : SmallMark n} (h : MarkControl A L t) (hLK : L≤K) :
    MarkControl A K t := fun d hd=>⟨(h d hd).1,(h d hd).2.trans hLK⟩

lemma MarkControl.prepend {A : ℝ} {L : ℕ} {t : SmallMark n} (h : MarkControl A L t)
    (P : OrdinaryWord n) (hp : wordBounded A P) : MarkControl A (L+P.length) (t.prepend P) := by
  intro d hd
  rcases h d hd with ⟨hb,hl⟩
  cases t with
  | diagonal Q s R=>
    simp only [SmallMark.prepend,SmallMark.diagnostic,List.length_append,List.length_cons] at *
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
    simp only [SmallMark.prepend,SmallMark.diagnostic] at *
    exact ⟨wordBounded_append hp hb,by simp only [List.length_append]; omega⟩

lemma MarkedControl.append {A : ℝ} {L : ℕ} {P Q : MarkedPolynomial n}
    (hp : MarkedControl A L P) (hq : MarkedControl A L Q) : MarkedControl A L (P++Q) := by
  intro t ht; rcases List.mem_append.mp ht with ht|ht
  · exact hp t ht
  · exact hq t ht

lemma MarkedControl.mono {A : ℝ} {L K : ℕ} {P : MarkedPolynomial n}
    (h : MarkedControl A L P) (hLK : L≤K) : MarkedControl A K P := fun t ht=>(h t ht).mono hLK

lemma MarkedControl.prepend {A : ℝ} {L : ℕ} {P : MarkedPolynomial n}
    (h : MarkedControl A L P) (w : OrdinaryWord n) (hw : wordBounded A w) :
    MarkedControl A (L+w.length) (P.prepend w) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
  exact (h s hs).prepend w hw

lemma MarkedControl.scale {A : ℝ} {L : ℕ} {P : MarkedPolynomial n}
    (h : MarkedControl A L P) (c : ℝ) : MarkedControl A L (P.scale c) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
  exact h s hs

lemma diagonalWords_control {A : ℝ} {L : ℕ} (hA : 1≤A) (s : Fin n→ℝ)
    (P : WordPolynomial (ι:=Fin n)) (hP : ∀t∈P,wordBounded A t.2 ∧ t.2.length≤L) :
    MarkedControl A (L+1) (diagonalWords s P) := by
  intro t ht d hd
  obtain ⟨r,hr,he⟩:=List.mem_map.mp ht
  subst t
  simp only [SmallMark.diagnostic,List.length_append,List.length_cons,List.length_nil]
  exact ⟨wordBounded_diag (hP r hr).1 d (fun i=>(hd i).trans hA),by have hh:=(hP r hr).2; omega⟩

lemma averageWords_control {A : ℝ} {L : ℕ} (c : ℝ) (s : Fin n→ℝ)
    (P : WordPolynomial (ι:=Fin n)) (hP : ∀t∈P,wordBounded A t.2 ∧ t.2.length≤L) :
    MarkedControl A L (averageWords c s P) := by
  intro t ht d hd
  obtain ⟨r,hr,he⟩:=List.mem_map.mp ht
  subst t
  exact hP r hr

lemma zeroPair_control {A : ℝ} {L : ℕ} (hL : 1≤L) : PairControl (n:=n) A L zeroPair := by
  constructor
  · intro t ht; have he:=List.mem_singleton.mp ht; subst t
    intro d hd; exact ⟨by intro l hl; simp [SmallMark.diagnostic] at hl,by simp [SmallMark.diagnostic]⟩
  · intro t ht; have he:=List.mem_singleton.mp ht; subst t
    intro d hd
    constructor
    · intro l hl
      have he : l=Letter.noise := by simpa [SmallMark.diagnostic] using hl
      subst l
      trivial
    · simpa [SmallMark.diagnostic] using hL

lemma smallBranch_control {A : ℝ} {L K : ℕ} (hA : 1≤A) (hLK : L+2≤K)
    (j : ℝ) (p : Fin n→ℝ) (T : SourceTree (Fin n→ℝ)) (V : Pair n)
    (hT : (∀t∈(T.words j).1,wordBounded A t.2 ∧ t.2.length≤L) ∧
      (∀t∈(T.words j).2,wordBounded A t.2 ∧ t.2.length≤L))
    (hV : PairControl A K V) : PairControl A K (smallBranch j p T V) := by
  have hd:=diagonalWords_control hA p _ hT.2
  have ha:=averageWords_control (-j) p _ hT.1
  have hn : wordBounded (n:=n) A [.noise] := by intro l hl; have he:=List.mem_singleton.mp hl; subst l; trivial
  refine ⟨(hd.mono (by omega)).append hV.1,?_⟩
  exact (((hd.prepend [.noise] hn).mono (by simp only [List.length_cons,List.length_nil]; omega)).append (ha.mono (by omega))).append hV.2

lemma boundedBranch_control {A : ℝ} {L K : ℕ} (hLK : L+2≤K)
    (j : ℝ) (p : Fin n→ℝ) (hp : ∀i,|p i|≤A) (U V : Pair n)
    (hU : PairControl A L U) (hV : PairControl A K V) : PairControl A K (boundedBranch j p U V) := by
  have hd : wordBounded (n:=n) A [.diag p] := by intro l hl; have he:=List.mem_singleton.mp hl; subst l; exact hp
  have hd' : wordBounded (n:=n) A [.noise,.diag p] := by
    intro l hl; simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
    rcases hl with rfl|rfl
    · trivial
    · exact hp
  refine ⟨((hU.2.prepend [.diag p] hd).mono (by simp only [List.length_singleton]; omega)).append hV.1,?_⟩
  exact (((hU.2.prepend [.noise,.diag p] hd').mono (by simp only [List.length_cons,List.length_nil]; omega)).append
    ((hU.1.scale _).mono (by omega))).append hV.2

end SKGapCutoff.Recipe

end
end

end OAI
