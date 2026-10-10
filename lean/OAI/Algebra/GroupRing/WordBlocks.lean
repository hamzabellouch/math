import Mathlib
import OAI.Algebra.GroupRing.ContiguousSplit

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.WordBlocks
open scoped Classical
open BlockBoundary
variable {A : Type*}
abbrev lengths (ws : List (List A)) : List ℕ := ws.map List.length
abbrev Occ (ws : List (List A)) := BlockBoundary.Occ (lengths ws)
lemma total_length (ws : List (List A)) : (lengths ws).sum=ws.flatten.length := by
  induction ws with
  | nil=>rfl
  | cons w ws ih=>simpa only [lengths,List.map_cons,List.sum_cons,List.flatten_cons,List.length_append] using congrArg (w.length+·) ih
def coordinates (ws : List (List A)) : Occ ws≃Fin ws.flatten.length :=
  (BlockBoundary.coordinates (lengths ws)).trans (finCongr (total_length ws))
def letter : (ws : List (List A))→Occ ws→A
  | [],x=>Empty.elim x
  | w::ws,x=>Sum.elim w.get (letter ws) x
lemma coordinates_inl (w : List A) (ws : List (List A)) (x : Fin w.length) :
    (coordinates (w::ws) (.inl x)).val=x.val := rfl
lemma coordinates_inr (w : List A) (ws : List (List A)) (x : Occ ws) :
    (coordinates (w::ws) (.inr x)).val=w.length+(coordinates ws x).val := rfl
lemma letter_eq (ws : List (List A)) (x : Occ ws) :
    letter ws x=ws.flatten.get (coordinates ws x) := by
  induction ws with
  | nil=>exact Empty.elim x
  | cons w ws ih=>
    cases x with
    | inl x=>
      change w[x.val]=((w++ws.flatten).get _)
      simp only [List.get_eq_getElem,coordinates_inl]
      rw [List.getElem_append_left x.isLt]
    | inr x=>
      rw [show letter (w::ws) (.inr x)=letter ws x from rfl,ih]
      change ws.flatten[(coordinates ws x).val]=
        (w++ws.flatten)[w.length+(coordinates ws x).val]'(by
          simpa only [List.length_append] using Nat.add_lt_add_left (coordinates ws x).isLt w.length)
      simpa only [Nat.add_comm] using List.getElem_append_right' w (coordinates ws x).isLt
lemma finRotate_congr {n m : ℕ} (h : n=m) :
    (finCongr h).symm.permCongr (finRotate m)=finRotate n := by subst m;rfl
lemma full_eq (ws : List (List A)) :
    (coordinates ws).symm.permCongr (finRotate ws.flatten.length)=
      BlockBoundary.full (lengths ws) := by
  change (BlockBoundary.coordinates (lengths ws)).symm.permCongr
    ((finCongr (total_length ws)).symm.permCongr (finRotate ws.flatten.length))=_
  rw [finRotate_congr]
  rfl
/-- A full inverse-letter matching on the separate literal word boundaries,
with actual combinatorial genus zero. This is not a PL-picture assertion. -/
structure Matching (inv : A→A) (ws : List (List A)) where
  partner : Equiv.Perm (Occ ws)
  involutive : Function.Involutive partner
  fixed_free : ∀x,partner x≠x
  compatible : ∀x,letter ws (partner x)=inv (letter ws x)
  genusZero : MapEuler.GenusZero (BlockBoundary.rotation (lengths ws)) partner

def ofDisk {inv : A→A} (ws : List (List A))
    (d : WordPairing.Data inv ws.flatten.get) : Matching inv ws where
  partner := (coordinates ws).symm.permCongr d.partner
  involutive := PermutationTransport.involutive _ _ d.involutive
  fixed_free := PermutationTransport.fixed_free _ _ d.distinct
  compatible x := by
    simp only [letter_eq,Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
    exact d.compatible _
  genusZero := by
    have hh := MapConjugation.genusZero (coordinates ws).symm _ _ d.genusZero
    rw [full_eq] at hh
    exact BoundaryRefinement.preserves (BlockBoundary.refinement (lengths ws)) _
      (PermutationTransport.involutive _ _ d.involutive) hh
/-- The literal free identity has a planar matching on its blocks, even if
some of the blocks are empty. No nonempty-relator premise is added. -/
theorem of_identity {B : Type*} (ws : List (List (B×Bool)))
    (h : FreeGroup.mk ws.flatten=1) : Nonempty (Matching WordPairing.inverseLetter ws) := by
  obtain ⟨d⟩ := WordPairing.of_identity h
  exact ⟨ofDisk ws d⟩

end TorsionFreeZeroDivisors.WordBlocks
namespace TorsionFreeZeroDivisors.AlgebraicPictures
open FreeGroup
variable {A I : Type*} (rel : I→List (A×Bool)) (outer : List (A×Bool))
def blockWords (ts : List (Term (A:=A) (I:=I))) : List (List (A×Bool)) :=
  invRev outer::ts.map (Term.word rel)
lemma blockWords_flatten (ts : List (Term (A:=A) (I:=I))) :
    (blockWords rel outer ts).flatten=cutWord rel outer ts := by
  simp only [blockWords,List.flatten_cons,←List.flatMap_def,cutWord,word]
/-- The algebraic null word yields a literal genus-zero matching after
separating the outer word and every conjugated relator into distinct cyclic
boundaries. Conjugator suppression and graph lifts are not assumed here. -/
theorem quotient_block_matching (h : PresentedGroup.mk (relations rel) (mk outer)=1) :
    ∃ts : List (Term (A:=A) (I:=I)),
      Nonempty (WordBlocks.Matching WordPairing.inverseLetter (blockWords rel outer ts)) := by
  obtain ⟨ts,ht⟩ := expansion rel (PresentedGroup.mk_eq_one_iff.mp h)
  refine ⟨ts,WordBlocks.of_identity _ ?_⟩
  rw [blockWords_flatten,cutWord,←mul_mk,←inv_mk,ht,inv_mul_cancel]

end TorsionFreeZeroDivisors.AlgebraicPictures

namespace TorsionFreeZeroDivisors.CyclicCaps
open scoped Classical
variable {R : Type} (n : ℕ)
abbrev O := Fin (n+2)⊕R
abbrev p : O (R:=R) n := .inl (Fin.last (n+1))
abbrev q : O (R:=R) n := .inl 0
lemma distinct : p (R:=R) n≠q n := by
  intro h
  have he := congrArg (fun x : Fin (n+2)=>x.val) (Sum.inl.inj h)
  simp only [Fin.val_last,Fin.val_zero] at he
  omega
def raise (i : Fin n) : Fin (n+2) := ⟨i.val+1,by omega⟩
def embed : Fin n⊕R→MatchingSurgery.Remaining (p (R:=R) n) (q n)
  | .inl i=>⟨.inl (raise n i),by
      constructor <;> intro h
      · have hh := congrArg Fin.val (Sum.inl.inj h)
        simp only [raise,Fin.val_last] at hh
        omega
      · have hh := congrArg Fin.val (Sum.inl.inj h)
        simp only [raise,Fin.val_zero] at hh
        omega⟩
  | .inr r=>⟨.inr r,by simp [p,q]⟩
lemma embed_injective : Function.Injective (embed (R:=R) n) := by
  intro x y he
  have hh := congrArg Subtype.val he
  cases x <;> cases y
  · apply congrArg Sum.inl
    apply Fin.ext
    have hh := congrArg Fin.val (Sum.inl.inj hh)
    simpa only [raise,embed,Nat.add_right_cancel_iff] using hh
  · cases hh
  · cases hh
  · exact congrArg Sum.inr (Sum.inr.inj hh)
lemma embed_surjective : Function.Surjective (embed (R:=R) n) := by
  rintro ⟨x,hp,hq⟩
  cases x with
  | inl i=>
    have hi0 : i.val≠0 := fun h=>hq (congrArg Sum.inl (Fin.ext h))
    have hilast : i.val≠n+1 := fun h=>hp (congrArg Sum.inl (Fin.ext h))
    let j : Fin n := ⟨i.val-1,by omega⟩
    refine ⟨.inl j,?_⟩
    apply Subtype.ext
    apply congrArg Sum.inl
    apply Fin.ext
    change (i.val-1)+1=i.val
    omega
  | inr r=>exact ⟨.inr r,rfl⟩
def coordinates : (Fin n⊕R)≃MatchingSurgery.Remaining (p (R:=R) n) (q n) :=
  Equiv.ofBijective (embed n) ⟨embed_injective n,embed_surjective n⟩
variable (ρ : Equiv.Perm R)
def rotation : Equiv.Perm (O (R:=R) n) := Equiv.sumCongr (finRotate (n+2)) ρ
lemma next : rotation n ρ (p n)=q n := by simp [rotation,p,q]
lemma rotation_commutes (x : Fin n⊕R) :
    Tightening.rotation (rotation n ρ) (p n) (q n) (distinct n) (next n ρ) (coordinates n x)=
      coordinates n (Equiv.sumCongr (finRotate n) ρ x) := by
  let : DecidableEq (O (R:=R) n) := fun _ _=>Classical.propDecidable _
  apply Subtype.ext
  change Equiv.swap (p n) (rotation n ρ (q n))
    (rotation n ρ (embed n x))=(embed n (Equiv.sumCongr (finRotate n) ρ x)).val
  cases x with
  | inr r=>simp [rotation,embed,p,q,Equiv.swap_apply_def]
  | inl i=>
    have hr : (finRotate (n+2) (raise n i)).val=i.val+2 := by
      rw [ContiguousSplit.rotate_val]
      split_ifs with h
      all_goals dsimp only [raise] at *
      all_goals omega
    have hz : (finRotate (n+2) (0 : Fin (n+2))).val=1 := by
      rw [ContiguousSplit.rotate_val,ite_eq_right (by simp only [Fin.val_zero];omega)]
      rfl
    by_cases hi : i.val+1=n
    · have hp : rotation n ρ (embed (R:=R) n (.inl i)).val=p n := by
        apply congrArg Sum.inl
        apply Fin.ext
        exact hr.trans (by simp only [Fin.val_last];omega)
      rw [hp,Equiv.swap_apply_left]
      apply congrArg Sum.inl
      apply Fin.ext
      change (finRotate (n+2) (0 : Fin (n+2))).val=(finRotate n i).val+1
      rw [hz,ContiguousSplit.rotate_val,ite_eq_left hi]
    · have hp : rotation n ρ (embed (R:=R) n (.inl i)).val≠p n := by
        intro hh
        have hh := congrArg Fin.val (Sum.inl.inj hh)
        change (finRotate (n+2) (raise n i)).val=n+1 at hh
        rw [hr] at hh
        omega
      have hq : rotation n ρ (embed (R:=R) n (.inl i)).val≠rotation n ρ (q n) := by
        intro hh
        have hh := (rotation n ρ).injective hh
        exact (embed (R:=R) n (.inl i)).property.2 hh
      rw [Equiv.swap_apply_of_ne_of_ne hp hq]
      apply congrArg Sum.inl
      apply Fin.ext
      change (finRotate (n+2) (raise n i)).val=(finRotate n i).val+1
      rw [hr,ContiguousSplit.rotate_val,ite_eq_right hi]
lemma rotation_conjugate :
    Tightening.rotation (rotation n ρ) (p n) (q n) (distinct n) (next n ρ)=
      (coordinates n).permCongr (Equiv.sumCongr (finRotate n) ρ) := by
  apply Equiv.ext
  intro x
  obtain ⟨x,rfl⟩ := (coordinates n).surjective x
  rw [rotation_commutes]
  simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]
variable [Fintype R]
variable (α : Equiv.Perm (O (R:=R) n)) (hi : Function.Involutive α) (hf : ∀x,α x≠x)
def partner : Equiv.Perm (Fin n⊕R) :=
  (coordinates n).symm.permCongr (MatchingSurgery.partner α hi hf (p n) (q n) (distinct n))
omit [Fintype R] in
lemma involutive : Function.Involutive (partner n α hi hf) :=
  PermutationTransport.involutive _ _ (MatchingSurgery.involutive α hi hf (p n) (q n) (distinct n))
omit [Fintype R] in
lemma fixed_free (x : Fin n⊕R) : partner n α hi hf x≠x :=
  PermutationTransport.fixed_free _ _ (MatchingSurgery.distinct α hi hf (p n) (q n) (distinct n)) x
/-- Removing the two literal end letters of a cyclic block preserves genus
zero with the forced matching splice. The enclosed block may be empty. -/
theorem genusZero (hz : MapEuler.GenusZero (rotation n ρ) α) :
    MapEuler.GenusZero (Equiv.sumCongr (finRotate n) ρ) (partner n α hi hf) := by
  let : DecidableEq (O (R:=R) n) := fun _ _=>Classical.propDecidable _
  have hh := Tightening.genusZero (rotation n ρ) (p n) (q n) (distinct n) (next n ρ) α hi hf hz
  rw [rotation_conjugate] at hh
  have ht := MapConjugation.genusZero (coordinates n).symm _ _ hh
  have he : (coordinates n).symm.permCongr
      ((coordinates n).permCongr (Equiv.sumCongr (finRotate n) ρ))=
      Equiv.sumCongr (finRotate n) ρ := by
    apply Equiv.ext
    intro x
    simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.symm_apply_apply]
  rw [he] at ht
  exact ht
variable {A : Type*} (inv : A→A) (hinv : Function.Involutive inv) (label : O (R:=R) n→A)
  (hc : ∀x,label (α x)=inv (label x)) (hl : label (q n)=inv (label (p n)))
include hinv hc hl in
omit [Fintype R] in
lemma compatible (x : Fin n⊕R) :
    label (embed n (partner n α hi hf x))=inv (label (embed n x)) := by
  have hh := MatchingSurgery.compatible α hi hf (p n) (q n) (distinct n) inv hinv label hc hl (coordinates n x)
  convert hh using 1
  change label ((coordinates n) ((coordinates n).symm ((MatchingSurgery.partner α hi hf (p n) (q n) (distinct n))
    (coordinates n x))))=_
  rw [Equiv.apply_symm_apply]
  all_goals rfl

end TorsionFreeZeroDivisors.CyclicCaps
namespace TorsionFreeZeroDivisors.WordBlocks

section
open scoped Classical
variable {A : Type*} {inv : A→A} {ws vs : List (List A)}
def Matching.rename (d : Matching inv ws) (e : Occ ws≃Occ vs)
    (hl : ∀x,letter vs (e x)=letter ws x)
    (hr : ∀x,e (BlockBoundary.rotation (lengths ws) x)=BlockBoundary.rotation (lengths vs) (e x)) :
    Matching inv vs where
  partner := e.permCongr d.partner
  involutive := PermutationTransport.involutive _ _ d.involutive
  fixed_free := PermutationTransport.fixed_free _ _ d.fixed_free
  compatible x := by
    obtain ⟨x,rfl⟩ := e.surjective x
    simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply,hl]
    exact d.compatible x
  genusZero := by
    have hh := MapConjugation.genusZero e _ _ d.genusZero
    have he : e.permCongr (BlockBoundary.rotation (lengths ws))=BlockBoundary.rotation (lengths vs) := by
      apply Equiv.ext
      intro x
      obtain ⟨x,rfl⟩ := e.surjective x
      simpa only [Equiv.permCongr_apply,Equiv.symm_apply_apply] using hr x
    rwa [he] at hh

def exchange {X Y Z : Type} : (X⊕(Y⊕Z))≃(Y⊕(X⊕Z)) where
  toFun
    | .inl x=>.inr (.inl x)
    | .inr (.inl y)=>.inl y
    | .inr (.inr z)=>.inr (.inr z)
  invFun
    | .inl y=>.inr (.inl y)
    | .inr (.inl x)=>.inl x
    | .inr (.inr z)=>.inr (.inr z)
  left_inv x := by rcases x with x|y|z <;> rfl
  right_inv x := by rcases x with x|y|z <;> rfl
lemma exchange_rotation {X Y Z : Type} (f : Equiv.Perm X) (g : Equiv.Perm Y) (h : Equiv.Perm Z)
    (x : X⊕(Y⊕Z)) :
    exchange (Equiv.sumCongr f (Equiv.sumCongr g h) x)=
      Equiv.sumCongr g (Equiv.sumCongr f h) (exchange x) := by
  rcases x with x|y|z <;> rfl
lemma exchange_letter {X Y Z : Type} (f : X→A) (g : Y→A) (h : Z→A) (x : X⊕(Y⊕Z)) :
    Sum.elim g (Sum.elim f h) (exchange x)=Sum.elim f (Sum.elim g h) x := by
  rcases x with x|y|z <;> rfl
/-- Expose any literal word block while retaining all other blocks, in order. -/
def focus (pre : List (List A)) (w : List A) (suffix : List (List A)) :
    Occ (pre++w::suffix)≃Occ (w::(pre++suffix)) := match pre with
  | []=>Equiv.refl _
  | v::pre=>(Equiv.sumCongr (Equiv.refl (Fin v.length)) (focus pre w suffix)).trans exchange
lemma focus_letter (pre : List (List A)) (w : List A) (suffix : List (List A))
    (x : Occ (pre++w::suffix)) :
    letter (w::(pre++suffix)) (focus pre w suffix x)=letter (pre++w::suffix) x := by
  induction pre with
  | nil=>rfl
  | cons v pre ih=>
    cases x with
    | inl x=>rfl
    | inr x=>
      change Sum.elim w.get (Sum.elim v.get (letter (pre++suffix)))
        (exchange (.inr (focus pre w suffix x)))=letter (pre++w::suffix) x
      rw [exchange_letter]
      exact ih x
lemma focus_rotation (pre : List (List A)) (w : List A) (suffix : List (List A))
    (x : Occ (pre++w::suffix)) :
    focus pre w suffix (BlockBoundary.rotation (lengths (pre++w::suffix)) x)=
      BlockBoundary.rotation (lengths (w::(pre++suffix))) (focus pre w suffix x) := by
  induction pre with
  | nil=>rfl
  | cons v pre ih=>
    cases x with
    | inl x=>rfl
    | inr x=>
      change exchange (.inr (focus pre w suffix (BlockBoundary.rotation (lengths (pre++w::suffix)) x)))=
        Equiv.sumCongr (finRotate w.length)
          (Equiv.sumCongr (finRotate v.length) (BlockBoundary.rotation (lengths (pre++suffix))))
            (exchange (.inr (focus pre w suffix x)))
      rw [ih]
      exact exchange_rotation (finRotate v.length) (finRotate w.length)
        (BlockBoundary.rotation (lengths (pre++suffix))) (.inr (focus pre w suffix x))
variable {w : List A}
def Matching.focus (d : Matching inv (ws++w::vs)) : Matching inv (w::(ws++vs)) :=
  d.rename (WordBlocks.focus ws w vs) (focus_letter ws w vs) (focus_rotation ws w vs)
def Matching.unfocus (d : Matching inv (w::(ws++vs))) : Matching inv (ws++w::vs) :=
  d.rename (WordBlocks.focus ws w vs).symm
    (fun x=>by simpa using (focus_letter ws w vs ((WordBlocks.focus ws w vs).symm x)).symm)
    (fun x=>by
      apply (WordBlocks.focus ws w vs).injective
      simpa only [Equiv.apply_symm_apply] using (focus_rotation ws w vs ((WordBlocks.focus ws w vs).symm x)).symm)

end
open scoped Classical
variable {A : Type*} {inv : A→A} (hinv : Function.Involutive inv)
variable (a : A) (w : List A) (ws : List (List A))
def capCoordinates : Occ ((a::(w++[inv a]))::ws)≃CyclicCaps.O (R:=Occ ws) w.length :=
  Equiv.sumCongr (finCongr (by simp)) (Equiv.refl _)
lemma capRotation : (capCoordinates (inv:=inv) a w ws).permCongr
    (BlockBoundary.rotation (lengths ((a::(w++[inv a]))::ws)))=
      CyclicCaps.rotation w.length (BlockBoundary.rotation (lengths ws)) := by
  apply Equiv.ext
  intro x
  cases x with
  | inl i=>
    apply congrArg Sum.inl
    have h : (a::(w++[inv a])).length=w.length+2 := by simp
    exact Equiv.congr_fun (finRotate_congr h.symm) i
  | inr i=>rfl
abbrev capLabel := fun x:CyclicCaps.O (R:=Occ ws) w.length=>
  letter ((a::(w++[inv a]))::ws) ((capCoordinates (inv:=inv) a w ws).symm x)
lemma capLabel_q : capLabel (inv:=inv) a w ws (CyclicCaps.q w.length)=a := by rfl
lemma capLabel_p : capLabel (inv:=inv) a w ws (CyclicCaps.p w.length)=inv a := by
  change (a::(w++[inv a]))[w.length+1]=inv a
  simp
lemma capLabel_embed (x : Occ (w::ws)) :
    capLabel (inv:=inv) a w ws (CyclicCaps.embed w.length x)=letter (w::ws) x := by
  cases x with
  | inl i=>
    change (a::(w++[inv a]))[i.val+1]=w[i.val]
    simp only [List.getElem_cons_succ,List.getElem_append_left i.isLt]
  | inr i=>rfl
/-- Tighten inverse end caps of one literal word boundary. The matching is
spliced, and its genuine genus zero remains valid even for an empty interior. -/
def Matching.removeCaps (d : Matching inv ((a::(w++[inv a]))::ws)) : Matching inv (w::ws) := by
  let e := capCoordinates (inv:=inv) a w ws
  let α := e.permCongr d.partner
  have hi : Function.Involutive α := PermutationTransport.involutive e d.partner d.involutive
  have hf : ∀x,α x≠x := PermutationTransport.fixed_free e d.partner d.fixed_free
  have hz : MapEuler.GenusZero (CyclicCaps.rotation w.length (BlockBoundary.rotation (lengths ws))) α := by
    have ht := MapConjugation.genusZero e _ _ d.genusZero
    rwa [show e.permCongr (BlockBoundary.rotation (lengths ((a::(w++[inv a]))::ws)))=
      CyclicCaps.rotation w.length (BlockBoundary.rotation (lengths ws)) from capRotation a w ws] at ht
  have hc : ∀x,capLabel (inv:=inv) a w ws (α x)=inv (capLabel (inv:=inv) a w ws x) := by
    intro x
    simpa only [capLabel,α,e,Equiv.permCongr_apply,Equiv.symm_apply_apply] using d.compatible (e.symm x)
  refine ⟨CyclicCaps.partner w.length α hi hf,
    CyclicCaps.involutive w.length α hi hf,
    CyclicCaps.fixed_free w.length α hi hf,?_,CyclicCaps.genusZero w.length _ α hi hf hz⟩
  intro x
  have hh := CyclicCaps.compatible w.length α hi hf inv hinv (capLabel (inv:=inv) a w ws) hc
    (by rw [capLabel_q,capLabel_p,hinv]) x
  rw [capLabel_embed a w ws (CyclicCaps.partner w.length α hi hf x),capLabel_embed a w ws x] at hh
  exact hh

end TorsionFreeZeroDivisors.WordBlocks

end

end OAI
