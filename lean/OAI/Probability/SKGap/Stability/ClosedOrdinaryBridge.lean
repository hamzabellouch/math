import Mathlib
import OAI.Probability.SKGap.Matrix.PrimaryWordControl
import OAI.Probability.SKGap.Localization.ClosedMarkedControl

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.ClosedMarked
open SKGapCutoff.Recipe Primary Primary.Tensor.Series
variable {n : ℕ}

lemma ordinary_mass_bridge (j : ℝ) (t : SourceTree (Fin n→ℝ)) :
    Marked.mass (GradedWords.ordinaryWords j t).1=MarkedPolynomial.mass (t.words j).1 ∧
    Marked.mass (GradedWords.ordinaryWords j t).2=MarkedPolynomial.mass (t.words j).2 := by
  have happend (p q : GradedWords (Fin n)) : Marked.mass (p++q)=Marked.mass p+Marked.mass q := by simp [Marked.mass]
  have hprepend (l : WordLetter (Fin n)) (p : GradedWords (Fin n)) : Marked.mass (GradedWords.prepend l p)=Marked.mass p := by
    simp [Marked.mass,GradedWords.prepend,List.map_map,Function.comp_def]
  have hbump (p : GradedWords (Fin n)) : Marked.mass (GradedWords.bump p)=Marked.mass p := by
    simp [Marked.mass,GradedWords.bump,List.map_map,Function.comp_def]
  have hscale (c : ℝ) (p : GradedWords (Fin n)) : Marked.mass (GradedWords.scale c p)=|c| *Marked.mass p := by
    induction p with
    | nil=>simp [Marked.mass,GradedWords.scale]
    | cons t p ih=>simpa [Marked.mass,GradedWords.scale,mul_add,abs_mul] using congrArg (fun r=>|c*t.1|+r) ih
  have hprefix (w : OrdinaryWord n) (p : WordPolynomial (ι:=Fin n)) : MarkedPolynomial.mass (prependWords w p)=MarkedPolynomial.mass p := by
    simp [MarkedPolynomial.mass,prependWords,List.map_map,Function.comp_def]
  have hscale' (c : ℝ) (p : WordPolynomial (ι:=Fin n)) : MarkedPolynomial.mass (scale c p)=|c| *MarkedPolynomial.mass p := by
    induction p with
    | nil=>simp [MarkedPolynomial.mass,scale]
    | cons t p ih=>simpa [MarkedPolynomial.mass,scale,mul_add,abs_mul] using congrArg (fun r=>|c*t.1|+r) ih
  have happend' (p q : WordPolynomial (ι:=Fin n)) : MarkedPolynomial.mass (p++q)=MarkedPolynomial.mass p+MarkedPolynomial.mass q := by simp [MarkedPolynomial.mass]
  induction t with
  | leaf c=>simp [GradedWords.ordinaryWords,GradedWords.scalar,SourceTree.words,Marked.mass,MarkedPolynomial.mass,GradedWords.bump,GradedWords.prepend]
  | branch p t u ih1 ih2=>
    simp only [GradedWords.ordinaryWords,SourceTree.words,GradedWords.branch,happend,hprepend,hbump,hscale,happend',hprefix,hscale',ih1.1,ih1.2,ih2.1,ih2.2,and_self]
end SKGap.Noncrossing.ClosedMarked

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.ClosedMarked
open SKGapCutoff.Recipe Primary Primary.Tensor.Series
variable {n : ℕ}

lemma ordinary_word_bridge (j : ℝ) (t : SourceTree (Fin n→ℝ)) :
    ((GradedWords.ordinaryWords j t).1.map (fun s=>s.2.2))=((t.words j).1.map (fun s=>liftWord s.2)) ∧
    ((GradedWords.ordinaryWords j t).2.map (fun s=>s.2.2))=((t.words j).2.map (fun s=>liftWord s.2)) := by
  have hprefix (l : WordLetter (Fin n)) (P : GradedWords (Fin n)) :
      (GradedWords.prepend l P).map (fun s=>s.2.2)=(P.map (fun s=>s.2.2)).map (fun w=>l::w) := by
    simp [GradedWords.prepend,List.map_map,Function.comp_def]
  have hprefix' (l : Letter (Fin n→ℝ)) (P : WordPolynomial (ι:=Fin n)) :
      (prependWords [l] P).map (fun s=>liftWord s.2)=(P.map (fun s=>liftWord s.2)).map (fun w=>l.toWord::w) := by
    simp [prependWords,liftWord,List.map_map,Function.comp_def]
  have hprefix'' (l m : Letter (Fin n→ℝ)) (P : WordPolynomial (ι:=Fin n)) :
      (prependWords [l,m] P).map (fun s=>liftWord s.2)=(P.map (fun s=>liftWord s.2)).map (fun w=>l.toWord::m.toWord::w) := by
    simp [prependWords,liftWord,List.map_map,Function.comp_def]
  induction t with
  | leaf c=>simp [GradedWords.ordinaryWords,GradedWords.scalar,GradedWords.bump,GradedWords.prepend,SourceTree.words,liftWord,Letter.toWord]
  | branch p t u ih1 ih2=>
    simp only [GradedWords.ordinaryWords,GradedWords.branch,SourceTree.words,List.map_append]
    simp only [GradedWords.bump,GradedWords.scale,List.map_map,Function.comp_def]
    change ((GradedWords.prepend (.diag p) (GradedWords.ordinaryWords j t).2).map (fun s=>s.2.2)++
      (GradedWords.ordinaryWords j u).1.map (fun s=>s.2.2)=_) ∧ _
    constructor
    · rw [hprefix,ih1.2,ih2.1,hprefix'];rfl
    · simp only [hprefix,ih1.1,ih1.2,ih2.2,hprefix'',scale,List.map_map,Function.comp_def]
      rfl

lemma ordinary_control_bridge (j : ℝ) (t : SourceTree (Fin n→ℝ)) {A : ℝ} {L : ℕ}
    (h : PolynomialControl A L (t.words j).1 ∧ PolynomialControl A L (t.words j).2) :
    GradedControl A L (GradedWords.ordinaryWords j t).1 ∧ GradedControl A L (GradedWords.ordinaryWords j t).2 := by
  have hb:=ordinary_word_bridge j t
  constructor
  · intro s hs
    have hh : s.2.2∈((GradedWords.ordinaryWords j t).1.map (fun s=>s.2.2)):=List.mem_map.mpr ⟨s,hs,rfl⟩
    rw [hb.1] at hh
    obtain ⟨v,hv,he⟩:=List.mem_map.mp hh
    rw [←he]
    exact ⟨closedWordBounded_lift (h.1 v hv).1,by simpa [liftWord] using (h.1 v hv).2⟩
  · intro s hs
    have hh : s.2.2∈((GradedWords.ordinaryWords j t).2.map (fun s=>s.2.2)):=List.mem_map.mpr ⟨s,hs,rfl⟩
    rw [hb.2] at hh
    obtain ⟨v,hv,he⟩:=List.mem_map.mp hh
    rw [←he]
    exact ⟨closedWordBounded_lift (h.2 v hv).1,by simpa [liftWord] using (h.2 v hv).2⟩
end SKGap.Noncrossing.ClosedMarked

end
end

end OAI
