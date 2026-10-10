import Mathlib
import OAI.Probability.SKGap.Localization.SeparateCut
import OAI.Probability.SKGap.Matrix.InverseDiagram

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
namespace SKGap.Noncrossing
namespace Diagram
variable {D E : Type*}

def append : Diagram D → Diagram D → Diagram D
  | .nil, e => e
  | .diag a d, e => .diag a (d.append e)
  | .arch a b, e => .arch a (b.append e)

@[simp] lemma append_word (d e : Diagram D) : (d.append e).word = d.word ++ e.word := by
  induction d with
  | nil => rfl
  | diag a d ih => simp [append,word,ih]
  | arch a b ia ib => simp [append,word,ib,List.append_assoc]

@[simp] lemma append_nil (d : Diagram D) : d.append .nil = d := by
  induction d with
  | nil => rfl
  | diag a d ih => simp [append,ih]
  | arch a b ia ib => simp [append,ib]

lemma append_assoc (d e f : Diagram D) : (d.append e).append f = d.append (e.append f) := by
  induction d with
  | nil => rfl
  | diag a d ih => simp [append,ih]
  | arch a b ia ib => simp [append,ib]

def map (f : D → E) : Diagram D → Diagram E
  | .nil => .nil
  | .diag a d => .diag (f a) (d.map f)
  | .arch a b => .arch (a.map f) (b.map f)

def Letter.map (f : D → E) : Letter D → Letter E
  | .diag a => .diag (f a)
  | .noise => .noise

@[simp] lemma map_word (f : D → E) (d : Diagram D) :
    (d.map f).word = d.word.map (Letter.map f) := by
  induction d with
  | nil => rfl
  | diag a d ih => simp [map,word,ih,Letter.map]
  | arch a b ia ib => simp [map,word,ia,ib,Letter.map]

@[simp] lemma map_append (f : D → E) (d e : Diagram D) :
    (d.append e).map f = (d.map f).append (e.map f) := by
  induction d with
  | nil => rfl
  | diag a d ih => simp [map,append,ih]
  | arch a b ia ib => simp [map,append,ib]

lemma remove_last_diag (d : Diagram D) (F : List (Letter D)) (a : D)
    (h : d.word = F ++ [.diag a]) :
    ∃ e : Diagram D, e.word=F ∧ d=e.append (.diag a .nil) := by
  induction d generalizing F with
  | nil => simp [word] at h
  | diag b d ih =>
    cases F with
    | nil =>
      simp only [List.nil_append,word,List.cons.injEq] at h
      obtain ⟨hb,hd⟩ := h
      have hab : b=a := Letter.diag.inj hb
      subst b
      have he : d=.nil := by cases d <;> simp [word] at hd ⊢
      subst d
      exact ⟨.nil,rfl,rfl⟩
    | cons c F =>
      simp only [List.cons_append,word,List.cons.injEq] at h
      obtain ⟨rfl,hd⟩ := h
      obtain ⟨e,he,hd⟩ := ih F hd
      refine ⟨.diag b e,?_,?_⟩
      · simp [word,he]
      · simp [append,hd]
  | arch b d ib ih =>
    cases F with
    | nil => simp [word] at h
    | cons c F =>
      simp only [List.cons_append,word,List.cons.injEq] at h
      obtain ⟨rfl,hd⟩ := h
      have hdlen : b.word.length+1≤F.length := by
        have hh := congrArg List.length hd
        simp only [List.length_append,List.length_cons,List.length_nil] at hh
        by_contra hc
        have hef : d.word=[] := by
          apply List.length_eq_zero_iff.mp
          omega
        rw [hef] at hd
        have hlast := congrArg List.getLast? hd
        simp at hlast
      have he : F = b.word ++ (.noise :: F.drop (b.word.length+1)) := by
        have hh := congrArg (List.take (b.word.length+1)) hd
        rw [List.take_append_of_le_length (l₁ := F) (l₂ := [.diag a]) hdlen] at hh
        simp only [List.take_append,
          List.take_of_length_le (show b.word.length ≤ b.word.length+1 by omega),
          Nat.add_sub_cancel_left, List.take_succ_cons,List.take_zero] at hh
        have hb : F.take (b.word.length+1)=b.word++[.noise] := hh.symm
        calc
          F = F.take (b.word.length+1) ++ F.drop (b.word.length+1) :=
            (List.take_append_drop _ _).symm
          _ = _ := by rw [hb]; simp
      rw [he,List.append_assoc,List.cons_append,List.append_cancel_left_eq,
        List.cons.injEq] at hd
      obtain ⟨_,ht⟩ := hd
      obtain ⟨e,he',hde⟩ := ih _ ht
      refine ⟨.arch b e,?_,?_⟩
      · simpa [word,he'] using he.symm
      · simp [append,hde]

end Diagram
end SKGap.Noncrossing

noncomputable section
namespace SKGap.Noncrossing
namespace Diagram
variable {D : Type*}

@[simp] lemma append_size (d e : Diagram D) : (d.append e).size = d.size+e.size := by
  induction d with
  | nil => simp [append,size]
  | diag a d ih => simp [append,size,ih]; omega
  | arch a b ia ib => simp [append,size,ib]; omega

lemma append_last_diag_injective (a : D) :
    Function.Injective (fun d : Diagram D => d.append (.diag a .nil)) := by
  intro d
  induction d with
  | nil =>
    intro e he
    cases e with
    | nil => rfl
    | diag b e =>
      have ht : Diagram.nil = e.append (.diag a .nil) := (Diagram.diag.inj he).2
      have hs := congrArg size ht
      simp [size] at hs
    | arch b e => cases he
  | diag b d ih =>
    intro e he
    cases e with
    | nil =>
      have ht : d.append (.diag a .nil) = Diagram.nil := (Diagram.diag.inj he).2
      have hs := congrArg size ht
      simp [size] at hs
    | diag c e =>
      obtain ⟨rfl,ht⟩ := Diagram.diag.inj he
      rw [ih ht]
    | arch c e => cases he
  | arch b d ib ih =>
    intro e he
    cases e with
    | nil => cases he
    | diag c e => cases he
    | arch c e =>
      obtain ⟨rfl,ht⟩ := Diagram.arch.inj he
      rw [ih ht]

lemma value_append {ι : Type*} [Fintype ι] (j : ℝ) (d e : Diagram (ι→ℝ)) (i : ι) :
    (d.append e).value j i = d.value j i * e.value j i := by
  induction d with
  | nil => simp [append,value]
  | diag a d ih => simp [append,value,ih,mul_assoc]
  | arch a b ia ib => simp [append,value,ib,mul_assoc]

end Diagram
namespace InverseDiagram

def expandBlocks (bs : List Bool) : List (Letter Bool) :=
  bs.flatMap (fun b => if b then [.diag true,.noise] else [.diag false])

@[simp] lemma expandBlocks_nil : expandBlocks [] = [] := rfl
@[simp] lemma expandBlocks_false (bs : List Bool) :
    expandBlocks (false::bs) = .diag false :: expandBlocks bs := rfl
@[simp] lemma expandBlocks_true (bs : List Bool) :
    expandBlocks (true::bs) = .diag true :: .noise :: expandBlocks bs := rfl
@[simp] lemma expandBlocks_append (bs cs : List Bool) :
    expandBlocks (bs++cs) = expandBlocks bs ++ expandBlocks cs := by
  simp [expandBlocks]

lemma split_noise (bs : List Bool) (U V : List (Letter Bool))
    (h : expandBlocks bs = U ++ (.noise::V)) :
    ∃ p q : List Bool, bs=p++(true::q) ∧
      U=expandBlocks p++[.diag true] ∧ V=expandBlocks q := by
  induction bs generalizing U with
  | nil => simp at h
  | cons b bs ih =>
    cases b with
    | false =>
      cases U with
      | nil => simp at h
      | cons c U =>
        simp only [expandBlocks_false,List.cons_append,List.cons.injEq] at h
        obtain ⟨rfl,ht⟩ := h
        obtain ⟨p,q,hpq,hU,hV⟩ := ih U ht
        exact ⟨false::p,q,by simp [hpq],by simp [hU],hV⟩
    | true =>
      cases U with
      | nil => simp at h
      | cons c U =>
        simp only [expandBlocks_true,List.cons_append,List.cons.injEq] at h
        obtain ⟨rfl,ht⟩ := h
        cases U with
        | nil =>
          simp only [List.nil_append,List.cons.injEq,true_and] at ht
          exact ⟨[],bs,rfl,rfl,ht.symm⟩
        | cons c U =>
          simp only [List.cons_append,List.cons.injEq] at ht
          obtain ⟨rfl,ht⟩ := ht
          obtain ⟨p,q,hpq,hU,hV⟩ := ih U ht
          exact ⟨true::p,q,by simp [hpq],by simp [hU],hV⟩

def toDiagram : InverseDiagram → Diagram Bool
  | .empty => .nil
  | .counterterm d => .diag false (toDiagram d)
  | .arch u v => .diag true
      (.arch ((toDiagram u).append (.diag true .nil)) (toDiagram v))

@[simp] lemma toDiagram_word (d : InverseDiagram) :
    d.toDiagram.word = expandBlocks d.blocks := by
  induction d with
  | empty => rfl
  | counterterm d ih => simp [toDiagram,Diagram.word,blocks,ih]
  | arch u v iu iv => simp [toDiagram,Diagram.word,blocks,iu,iv,List.append_assoc]

lemma toDiagram_injective : Function.Injective toDiagram := by
  intro d
  induction d with
  | empty => intro e he; cases e <;> cases he; rfl
  | counterterm d ih =>
    intro e he
    cases e with
    | empty => cases he
    | counterterm e => exact congrArg counterterm (ih (Diagram.diag.inj he).2)
    | arch u v => cases he
  | arch u v iu iv =>
    intro e he
    cases e with
    | empty => cases he
    | counterterm e => cases he
    | arch x y =>
      have ht := Diagram.arch.inj (Diagram.diag.inj he).2
      rw [iu (Diagram.append_last_diag_injective true ht.1),iv ht.2]

lemma toDiagram_surjective (d : Diagram Bool) (bs : List Bool)
    (h : d.word=expandBlocks bs) :
    ∃ e : InverseDiagram, e.blocks=bs ∧ e.toDiagram=d := by
  induction hs : d.size using Nat.strong_induction_on generalizing d bs with
  | h n ih =>
    cases bs with
    | nil =>
      have hd : d=.nil := by cases d <;> simp [Diagram.word] at h ⊢
      subst d
      exact ⟨.empty,rfl,rfl⟩
    | cons b bs =>
      cases b with
      | false =>
        cases d with
        | nil => simp [Diagram.word] at h
        | arch u v => simp [Diagram.word] at h
        | diag a d =>
          simp only [Diagram.word,expandBlocks_false,List.cons.injEq,Letter.diag.injEq] at h
          obtain ⟨rfl,hd⟩ := h
          obtain ⟨e,he,hed⟩ := ih d.size (by simp [Diagram.size] at hs; omega) d bs hd rfl
          exact ⟨.counterterm e,by simp [blocks,he],by simp [toDiagram,hed]⟩
      | true =>
        cases d with
        | nil => simp [Diagram.word] at h
        | arch u v => simp [Diagram.word] at h
        | diag a d =>
          simp only [Diagram.word,expandBlocks_true,List.cons.injEq,Letter.diag.injEq] at h
          obtain ⟨rfl,hd⟩ := h
          cases d with
          | nil => simp [Diagram.word] at hd
          | diag a d => simp [Diagram.word] at hd
          | arch u v =>
            simp only [Diagram.word,List.cons.injEq,true_and] at hd
            obtain ⟨p,q,hbs,hu,hv⟩ := split_noise bs u.word v.word hd.symm
            obtain ⟨u',hu',huu⟩ := u.remove_last_diag (expandBlocks p) true hu
            have hnu : u'.size<n := by
              rw [huu] at hs
              simp only [Diagram.size,Diagram.append_size] at hs
              omega
            have hnv : v.size<n := by simp only [Diagram.size] at hs; omega
            obtain ⟨e,he,heu⟩ := ih u'.size hnu u' p hu' rfl
            obtain ⟨f,hf,hfv⟩ := ih v.size hnv v q hv rfl
            refine ⟨.arch e f,?_,?_⟩
            · simp [blocks,he,hf,hbs]
            · simp [toDiagram,heu,hfv,huu]

end InverseDiagram
end SKGap.Noncrossing

noncomputable section
open scoped BigOperators

end
end
end
end
end
end

end OAI
