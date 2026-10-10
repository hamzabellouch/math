import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.TapeTools
import OAI.Combinatorics.MatchingCount.Tapes.Codec

namespace OAI

namespace MatchingFPRAS.LiteralTape
open Turing MachineCost

variable {Λ σ : Type}
lemma scan_left (M : Λ→TM1.Stmt Symbol Λ σ) (l : Λ) (mark : Symbol)
    (hs : ∀ v T,T.head≠mark→TM1.stepAux (M l) v T=⟨some l,v,T.move .left⟩)
    (xs L R : List Symbol) (v : σ) (hx : ∀ a∈xs,a≠mark) :
    Exec M ⟨some l,v,(Tape.mk₂ (xs++mark::L) R).move .left⟩
      ⟨some l,v,Tape.mk₂ L (mark::(xs.reverse++R))⟩ xs.length := by
  induction xs generalizing R with
  | nil => simpa using Exec.refl M (⟨some l,v,Tape.mk₂ L (mark::R)⟩ : TM1.Cfg Symbol Λ σ)
  | cons a xs ih =>
    simp only [List.cons_append,mk₂_left]
    have h1:=Exec.step M l v (Tape.mk₂ (xs++mark::L) (a::R))
    rw [hs v _ (by simpa using hx a (by simp))] at h1
    have h2:=ih (a::R) (fun b hb=>hx b (by simp [hb]))
    have h:=h1.trans h2
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_comm] using h
lemma scan_right (M : Λ→TM1.Stmt Symbol Λ σ) (l : Λ) (mark : Symbol)
    (hs : ∀ v T,T.head≠mark→TM1.stepAux (M l) v T=⟨some l,v,T.move .right⟩)
    (xs L R : List Symbol) (v : σ) (hx : ∀ a∈xs,a≠mark) :
    Exec M ⟨some l,v,Tape.mk₂ L (xs++mark::R)⟩
      ⟨some l,v,Tape.mk₂ (xs.reverse++L) (mark::R)⟩ xs.length := by
  induction xs generalizing L with
  | nil => exact Exec.refl M _
  | cons a xs ih =>
    simp only [List.cons_append]
    have h1:=Exec.step M l v (Tape.mk₂ L (a::(xs++mark::R)))
    rw [hs v _ (by simpa using hx a (by simp)),mk₂_right] at h1
    have h2:=ih (a::L) (fun b hb=>hx b (by simp [hb]))
    have h:=h1.trans h2
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_comm] using h
end MatchingFPRAS.LiteralTape

namespace MatchingFPRAS.LiteralBlockMap
open Turing LiteralTape

inductive Label
  | start | read | seek | back | stopSep | stopOut
  deriving DecidableEq, Inhabited
instance : Fintype Label := ⟨{.start,.read,.seek,.back,.stopSep,.stopOut}, by intro a; cases a <;> simp⟩
abbrev Block (w : ℕ) := Fin w→Symbol
noncomputable def code (w : ℕ) (h : Block w→List Symbol) (header : List Symbol) :
    Label→TM1.Stmt Symbol Label (Block w)
  | .start => .move .left (.write (fun _ _=>7) (.move .left (.write (fun _ _=>6)
      (.move .right (.move .right (.goto (fun _ _=>.read)))))))
  | .read => grab (List.finRange w)
      (.branch (fun _ b=>decide (b=fun _=>0))
        (.move .left (.goto (fun _ _=>.stopSep)))
        (.move .left (.write (fun _ _=>7) (eraseToLeft w (.move .left (.goto (fun _ _=>.seek)))))))
  | .seek => .branch (fun a _=>decide (a=6))
      (select Finset.univ.toList (fun b=>.write (fun _ _=>0)
        (writeLeft (h b).reverse (.write (fun _ _=>6) (.move .right (.goto (fun _ _=>.back)))))) .halt)
      (.move .left (.goto (fun _ _=>.seek)))
  | .back => .branch (fun a _=>decide (a=7))
      (.move .right (.goto (fun _ _=>.read)))
      (.move .right (.goto (fun _ _=>.back)))
  | .stopSep => .branch (fun a _=>decide (a=7))
      (.write (fun _ _=>0) (.move .left (.goto (fun _ _=>.stopOut))))
      (.move .left (.goto (fun _ _=>.stopSep)))
  | .stopOut => .branch (fun a _=>decide (a=6))
      (.write (fun _ _=>0) (writeLeft header.reverse (.write (fun _ _=>0) (.move .right .halt))))
      (.move .left (.goto (fun _ _=>.stopOut)))
variable (w : ℕ) (h : Block w→List Symbol) (header : List Symbol)
local notation "M" => code w h header
lemma seek_path (v : Block w) (T : Tape Symbol) (ht : T.head≠6) :
    TM1.stepAux (M .seek) v T=⟨some .seek,v,T.move .left⟩ := by
  simp only [code,TM1.stepAux,ht,decide_false,Bool.cond_false]
lemma back_path (v : Block w) (T : Tape Symbol) (ht : T.head≠7) :
    TM1.stepAux (M .back) v T=⟨some .back,v,T.move .right⟩ := by
  simp only [code,TM1.stepAux,ht,decide_false,Bool.cond_false]
lemma stopSep_path (v : Block w) (T : Tape Symbol) (ht : T.head≠7) :
    TM1.stepAux (M .stopSep) v T=⟨some .stopSep,v,T.move .left⟩ := by
  simp only [code,TM1.stepAux,ht,decide_false,Bool.cond_false]
lemma stopOut_path (v : Block w) (T : Tape Symbol) (ht : T.head≠6) :
    TM1.stepAux (M .stopOut) v T=⟨some .stopOut,v,T.move .left⟩ := by
  simp only [code,TM1.stepAux,ht,decide_false,Bool.cond_false]

def working (out : List Symbol) (gap : ℕ) (input : List Symbol) : Tape Symbol :=
  Tape.mk₂ (7::(List.replicate gap 0++out.reverse++[6])) input
lemma start_step (input : List Symbol) (v : Block w) :
    Exec M ⟨some .start,v,Tape.mk₁ input⟩ ⟨some .read,v,working [] 0 input⟩ 1 := by
  have hh:=Exec.step M .start v (Tape.mk₁ input)
  simpa only [code,TM1.stepAux,Tape.mk₁,mk₂_left_nil,mk₂_write,mk₂_right,working,List.replicate_zero,
    List.reverse_nil,List.nil_append] using hh

lemma seek_write (v : Block w) (R : List Symbol) :
    Exec M ⟨some .seek,v,Tape.mk₂ [] (6::R)⟩
      ⟨some .back,v,Tape.mk₂ [6] (h v++R)⟩ 1 := by
  have hh:=Exec.step M .seek v (Tape.mk₂ [] (6::R))
  simp only [code,TM1.stepAux,mk₂_head,decide_true,Bool.cond_true] at hh
  rw [select_step _ _ _ v (by simp)] at hh
  have hs:=writeLeft_step (Γ:=Symbol) (h v).reverse
    (.write (fun _ _=>6) (.move .right (.goto (fun _ _=>Label.back)))) v R
  simp only [Fin.default_eq_zero,List.reverse_reverse,List.cons_append,TM1.stepAux,mk₂_write,mk₂_right] at hs
  simpa only [TM1.stepAux,mk₂_write,hs] using hh
lemma stopOut_write (v : Block w) (R : List Symbol) :
    Exec M ⟨some .stopOut,v,Tape.mk₂ [] (6::R)⟩
      ⟨none,v,Tape.mk₂ [0] (header++R)⟩ 1 := by
  have hh:=Exec.step M .stopOut v (Tape.mk₂ [] (6::R))
  have hs:=writeLeft_step (Γ:=Symbol) header.reverse
    (.write (fun _ _=>0) (.move .right (.halt : TM1.Stmt Symbol Label (Block w)))) v R
  simp only [Fin.default_eq_zero,List.reverse_reverse,List.cons_append,TM1.stepAux,mk₂_write,mk₂_right] at hs
  simpa only [code,TM1.stepAux,mk₂_head,decide_true,Bool.cond_true,mk₂_write,hs] using hh

lemma read_block (hw : 0<w) (b v : Block w) (hb : b≠fun _=>0)
    (out input : List Symbol) (gap : ℕ) :
    Exec M ⟨some .read,v,working out gap (List.ofFn b++input)⟩
      ⟨some .seek,b,(Tape.mk₂ (List.replicate gap 0++out.reverse++[6])
        (List.replicate w 0++7::input)).move .left⟩ 1 := by
  have hh:=Exec.step M .read v (working out gap (List.ofFn b++input))
  change Exec M _ (TM1.stepAux (grab _ _) v _) 1 at hh
  rw [working,grab_fin] at hh
  simp only [TM1.stepAux,hb,decide_false,Bool.cond_false] at hh
  cases hr : (List.ofFn b).reverse with
  | nil => have hl:=congrArg List.length hr; simp at hl; omega
  | cons a xs =>
    have hl : (xs++[7]).length=w := by
      have hh:=congrArg List.length hr
      simp only [List.length_reverse,List.length_ofFn,List.length_cons] at hh
      simp only [List.length_append,List.length_singleton]; omega
    rw [hr] at hh
    simp only [List.cons_append,mk₂_left,mk₂_write] at hh
    rw [show xs++7::(List.replicate gap 0++out.reverse++[6])=
      (xs++[7])++(List.replicate gap 0++out.reverse++[6]) by simp] at hh
    have ht:=eraseToLeft_step (xs++[7]) (List.replicate gap 0++out.reverse++[6]) (7::input)
      (.move .left (.goto (fun _ _=>Label.seek))) b
    rw [hl] at ht
    rw [ht] at hh
    exact hh
lemma cycle (hw : 0<w) (b v : Block w) (hb : b≠fun _=>0)
    (out input : List Symbol) (gap : ℕ)
    (ho : ∀ a∈out,a≠6 ∧ a≠7) (hh : ∀ a∈h b,a≠6 ∧ a≠7) :
    Exec M ⟨some .read,v,working out gap (List.ofFn b++input)⟩
      ⟨some .read,b,working (h b++out) (gap+w) input⟩
      (3+2*(out.length+gap)+(h b).length+w) := by
  have ha:=read_block w h header hw b v hb out input gap
  have hx : ∀ a∈List.replicate gap (0:Symbol)++out.reverse,a≠6 := by
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · have := (List.eq_of_mem_replicate ha); subst a; decide
    · exact (ho a (List.mem_reverse.mp ha)).1
  have hs:=scan_left M .seek 6 (seek_path w h header)
    (List.replicate gap 0++out.reverse) [] (List.replicate w 0++7::input) b hx
  have he : (List.replicate gap (0:Symbol)++out.reverse).reverse++(List.replicate w 0++7::input)=
      out++List.replicate (gap+w) 0++7::input := by
    simp only [List.reverse_append,List.reverse_reverse,List.reverse_replicate,List.replicate_add,List.append_assoc]
  rw [he] at hs
  have ht:=seek_write w h header b (out++List.replicate (gap+w) 0++7::input)
  have hy : ∀ a∈h b++out++List.replicate (gap+w) (0:Symbol),a≠7 := by
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · rcases List.mem_append.mp ha with ha|ha
      · exact (hh a ha).2
      · exact (ho a ha).2
    · have := List.eq_of_mem_replicate ha; subst a; decide
  have hu:=scan_right M .back 7 (back_path w h header)
    (h b++out++List.replicate (gap+w) 0) [6] input b hy
  have hv:=Exec.step M .back b
    (Tape.mk₂ ((h b++out++List.replicate (gap+w) 0).reverse++[6]) (7::input))
  simp only [code,TM1.stepAux,mk₂_head,decide_true,Bool.cond_true,mk₂_right] at hv
  simp only [List.append_assoc] at ha hs ht hu hv
  have hh:=((ha.trans hs).trans ht).trans (hu.trans hv)
  simp only [working,List.append_assoc,List.reverse_append,List.reverse_replicate,List.length_append,
    List.length_replicate,List.length_reverse] at hh ⊢
  apply Exec.mono hh
  omega

lemma mk₂_blanks (L R : List Symbol) (n : ℕ) :
    Tape.mk₂ L (R++List.replicate n 0)=Tape.mk₂ L R := by
  simp only [Tape.mk₂,show (0:Symbol)=default from rfl,blank_append_zero]
lemma mk₂_replicate (L : List Symbol) (n : ℕ) :
    Tape.mk₂ L (List.replicate n 0)=Tape.mk₂ L [] := by
  simpa only [List.nil_append] using mk₂_blanks L [] n
lemma mk₂_zero_left (R : List Symbol) : Tape.mk₂ [0] R=Tape.mk₁ R := by
  change Tape.mk' (ListBlank.mk (List.replicate 1 (default:Symbol))) _=Tape.mk' (ListBlank.mk []) _
  rw [blank_zero]

lemma finish (v : Block w) (out : List Symbol) (gap : ℕ)
    (ho : ∀ a∈out,a≠6 ∧ a≠7) :
    Exec M ⟨some .read,v,working out gap []⟩
      ⟨none,(fun _=>0),Tape.mk₁ (header++out)⟩ (3+w+gap+out.length) := by
  have hz : List.ofFn (fun _ : Fin w=>(0:Symbol))=List.replicate w 0 := by simp
  have ha:=Exec.step M .read v (working out gap [])
  change Exec M _ (TM1.stepAux (grab _ _) v _) 1 at ha
  rw [working,←mk₂_blanks _ [] w] at ha
  simp only [List.nil_append,←hz] at ha
  rw [show List.ofFn (fun _ : Fin w=>(0:Symbol))=
    List.ofFn (fun _ : Fin w=>(0:Symbol))++[] by simp,grab_fin] at ha
  simp only [TM1.stepAux,decide_true,Bool.cond_true,hz,List.reverse_replicate] at ha
  have hs:=scan_left M .stopSep 7 (stopSep_path w h header) (List.replicate w 0)
    (List.replicate gap 0++out.reverse++[6]) [] (fun _=>0)
    (by intro a ha; have := List.eq_of_mem_replicate ha; subst a; decide)
  have ht:=Exec.step M .stopSep (fun _ : Fin w=>(0:Symbol))
    (Tape.mk₂ (List.replicate gap 0++out.reverse++[6]) (7::List.replicate w 0))
  simp only [code,TM1.stepAux,mk₂_head,decide_true,Bool.cond_true,mk₂_write] at ht
  have hx : ∀ a∈List.replicate gap (0:Symbol)++out.reverse,a≠6 := by
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · have := List.eq_of_mem_replicate ha; subst a; decide
    · exact (ho a (List.mem_reverse.mp ha)).1
  have hu:=scan_left M .stopOut 6 (stopOut_path w h header)
    (List.replicate gap 0++out.reverse) [] (0::List.replicate w 0) (fun _=>0) hx
  have hv:=stopOut_write w h header (fun _=>0)
    (out++List.replicate (gap+1+w) 0)
  have he : (List.replicate gap (0:Symbol)++out.reverse).reverse++(0::List.replicate w 0)=
      out++List.replicate (gap+1+w) 0 := by
    simp only [List.reverse_append,List.reverse_reverse,List.reverse_replicate,List.replicate_add,List.append_assoc,List.replicate_one,List.singleton_append]
  rw [he] at hu
  simp only [List.length_replicate,List.reverse_replicate,List.append_nil] at hs
  have hb:=((ha.trans hs).trans ht).trans (hu.trans hv)
  rw [←List.append_assoc,mk₂_blanks,mk₂_zero_left] at hb
  simp only [List.append_assoc,List.length_append,List.length_reverse,List.length_replicate] at hb
  simp only [List.append_nil,mk₂_replicate] at hb
  simp only [working,List.append_assoc]
  apply Exec.mono hb
  omega

def budget (H n s : ℕ) : ℕ := (n+1)*(3+w+H+2*(s+n*(H+w)))
lemma blocks (hw : 0<w) (bs : List (Block w)) (v : Block w) (out : List Symbol) (gap H : ℕ)
    (hb : ∀ b∈bs,b≠fun _=>0)
    (hh : ∀ b∈bs,∀ a∈h b,a≠6 ∧ a≠7)
    (hH : ∀ b∈bs,(h b).length≤H)
    (ho : ∀ a∈out,a≠6 ∧ a≠7) :
    Exec M ⟨some .read,v,working out gap (bs.flatMap List.ofFn)⟩
      ⟨none,(fun _=>0),Tape.mk₁ (header++bs.reverse.flatMap h++out)⟩
      (budget w H bs.length (out.length+gap)) := by
  induction bs generalizing v out gap with
  | nil =>
    simpa only [List.flatMap_nil,List.reverse_nil,List.append_nil,List.nil_append]
      using (finish w h header v out gap ho).mono (by simp only [budget,List.length_nil,Nat.zero_mul,Nat.zero_add,Nat.add_zero,Nat.one_mul]; omega)
  | cons b bs ih =>
    have ha:=cycle w h header hw b v (hb b (by simp)) out (bs.flatMap List.ofFn) gap ho (hh b (by simp))
    have hs:=ih b (h b++out) (gap+w)
      (fun a ha=>hb a (by simp [ha])) (fun a ha=>hh a (by simp [ha]))
      (fun a ha=>hH a (by simp [ha]))
      (by intro a ha; rcases List.mem_append.mp ha with ha|ha; exact hh b (by simp) a ha; exact ho a ha)
    have he:=ha.trans hs
    simp only [List.reverse_cons,List.flatMap_append,List.append_assoc,
      List.flatMap_cons] at he ⊢
    apply he.mono
    have hlen:=hH b (by simp)
    simp only [budget,List.length_cons,List.length_append]
    nlinarith

lemma computes (hw : 0<w) (bs : List (Block w)) (H : ℕ)
    (hb : ∀ b∈bs,b≠fun _=>0)
    (hh : ∀ b∈bs,∀ a∈h b,a≠6 ∧ a≠7)
    (hH : ∀ b∈bs,(h b).length≤H) :
    Exec M ⟨some .start,(fun _=>0),Tape.mk₁ (bs.flatMap List.ofFn)⟩
      ⟨none,(fun _=>0),Tape.mk₁ (header++bs.reverse.flatMap h)⟩
      (1+budget w H bs.length 0) := by
  have ha:=start_step w h header (bs.flatMap List.ofFn) (fun _=>0)
  have hs:=blocks w h header hw bs (fun _=>0) [] 0 H hb hh hH (by simp)
  simpa only [List.append_nil,List.length_nil,Nat.zero_add] using ha.trans hs

end MatchingFPRAS.LiteralBlockMap

end OAI
