import Mathlib
import OAI.Algebra.GroupRing.WordBlocks

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.WordBlocks
open scoped Classical
variable {A : Type*}
open FreeGroup
/-- Remove exactly the actual conjugating word, not a replacement reduced
representative. Each removal is the proved cap splice on the same boundary. -/
def Matching.removeConjugator (c w : List (A×Bool)) (ws : List (List (A×Bool)))
    (d : Matching WordPairing.inverseLetter ((c++w++invRev c)::ws)) :
    Matching WordPairing.inverseLetter (w::ws) := by
  induction c with
  | nil=>simpa only [List.nil_append,invRev_empty,List.append_nil] using d
  | cons a c ih=>
    have he : (a::c)++w++invRev (a::c)=a::((c++w++invRev c)++[WordPairing.inverseLetter a]) := by
      simp only [List.cons_append,invRev,WordPairing.inverseLetter,
        List.reverse_cons,List.map_cons,List.append_assoc]
    rw [he] at d
    exact ih (d.removeCaps WordPairing.inverseLetter_involutive a (c++w++invRev c) ws)

def Matching.removeConjugatorAt (c w : List (A×Bool)) (pre post : List (List (A×Bool)))
    (d : Matching WordPairing.inverseLetter (pre++(c++w++invRev c)::post)) :
    Matching WordPairing.inverseLetter (pre++w::post) :=
  (d.focus.removeConjugator c w (pre++post)).unfocus

end TorsionFreeZeroDivisors.WordBlocks
namespace TorsionFreeZeroDivisors.AlgebraicPictures
open FreeGroup
variable {A I : Type*} (rel : I→List (A×Bool))
def coreWords (ts : List (Term (A:=A) (I:=I))) : List (List (A×Bool)) := ts.map (Term.core rel)
def stripConjugators (ts : List (Term (A:=A) (I:=I)))
    (pre : List (List (A×Bool)))
    (d : WordBlocks.Matching WordPairing.inverseLetter (pre++ts.map (Term.word rel))) :
    WordBlocks.Matching WordPairing.inverseLetter (pre++coreWords rel ts) := by
  induction ts generalizing pre with
  | nil=>exact d
  | cons t ts ih=>
    change WordBlocks.Matching WordPairing.inverseLetter
      (pre++(t.connector++t.core rel++invRev t.connector)::ts.map (Term.word rel)) at d
    have d' := d.removeConjugatorAt t.connector (t.core rel) pre (ts.map (Term.word rel))
    have d'' := ih (pre++[t.core rel]) (by simpa only [List.append_assoc,List.singleton_append] using d')
    simpa only [List.append_assoc,List.singleton_append,coreWords,List.map_cons] using d''
/-- A literal quotient-null word supplies actual planar inverse-letter matching
on the outer inverse word and signed relator cores, with all conjugating paths
removed by genuine genus-zero preserving surgery. This is still finite
permutation data, not an assumed topological surface or graph lift. -/
theorem quotient_core_matching (outer : List (A×Bool))
    (h : PresentedGroup.mk (relations rel) (mk outer)=1) :
    ∃ts : List (Term (A:=A) (I:=I)),
      Nonempty (WordBlocks.Matching WordPairing.inverseLetter (invRev outer::coreWords rel ts)) := by
  obtain ⟨ts,⟨d⟩⟩ := quotient_block_matching rel outer h
  exact ⟨ts,⟨stripConjugators rel ts [invRev outer] d⟩⟩

end TorsionFreeZeroDivisors.AlgebraicPictures

namespace TorsionFreeZeroDivisors.GraphPresentation
open PortSubdivision
open scoped Classical
variable {V D : Type} (Γ : PortGraph V D)

/-- An ordinary port path; no reduction assumption, and loops and parallel
edges remain distinct. This is used for the exact graph relators. -/
inductive Path : V→V→Type
  | nil (v : V) : Path v v
  | cons (d : D) {b : V} (p : Path (Γ.origin (Γ.reverse d)) b) : Path (Γ.origin d) b
namespace Path
variable {Γ} {a b c : V}
def append : {a b c : V} → Path Γ a b→Path Γ b c→Path Γ a c
  | _,_,_,.nil _,q => q
  | _,_,_,.cons d p,q => .cons d (p.append q)
def single (d : D) : Path Γ (Γ.origin d) (Γ.origin (Γ.reverse d)) := .cons d (.nil _)
def cast {a b a' b' : V} (ha : a=a') (hb : b=b') (p : Path Γ a b) : Path Γ a' b' := by
  subst a'; subst b'; exact p
def reverse : Path Γ a b→Path Γ b a := by
  intro p
  induction p with
  | nil v => exact .nil v
  | cons d p ih =>
    exact (ih.append (single (Γ:=Γ) (Γ.reverse d))).cast rfl
      (congrArg Γ.origin (PortGraph.reverse_reverse_apply Γ d))

def eval {G : Type*} [Group G] (label : D→G) : {a b : V} → Path Γ a b→G
  | _,_,.nil _ => 1
  | _,_,.cons d p => label d*p.eval label
@[simp] lemma eval_nil {G : Type*} [Group G] (label : D→G) (v : V) :
    (Path.nil (Γ:=Γ) v).eval label=1 := rfl
@[simp] lemma eval_cons {G : Type*} [Group G] (label : D→G) (d : D)
    (p : Path Γ (Γ.origin (Γ.reverse d)) b) :
    (Path.cons d p).eval label=label d*p.eval label := rfl
@[simp] lemma eval_append {G : Type*} [Group G] (label : D→G)
    (p : Path Γ a b) (q : Path Γ b c) :
    (p.append q).eval label=p.eval label*q.eval label := by
  induction p with
  | nil v => simp [append]
  | cons d p ih => simp only [append,eval_cons,ih,mul_assoc]
@[simp] lemma eval_single {G : Type*} [Group G] (label : D→G) (d : D) :
    (single (Γ:=Γ) d).eval label=label d := by simp [single]
@[simp] lemma eval_cast {G : Type*} [Group G] (label : D→G)
    {a b a' b' : V} (ha : a=a') (hb : b=b') (p : Path Γ a b) :
    (p.cast ha hb).eval label=p.eval label := by
  subst a'; subst b'; rfl
lemma eval_reverse {G : Type*} [Group G] (label : D→G)
    (hl : ∀ d,label (Γ.reverse d)=(label d)⁻¹) (p : Path Γ a b) :
    p.reverse.eval label=(p.eval label)⁻¹ := by
  induction p with
  | nil v => simp [reverse]
  | cons d p ih =>
    simp only [reverse] at ih
    simp only [reverse, eval_cast, eval_append,eval_single,ih,hl,eval_cons,mul_inv_rev]

lemma eval_map {G H : Type*} [Group G] [Group H] (f : G→*H)
    (label : D→G) (p : Path Γ a b) :
    p.eval (fun d => f (label d))=f (p.eval label) := by
  induction p with
  | nil v => simp
  | cons d p ih => simp only [eval_cons,ih,map_mul]

end Path
end TorsionFreeZeroDivisors.GraphPresentation
namespace TorsionFreeZeroDivisors.GraphPresentation.Path
open PortSubdivision
variable {V D : Type} {Γ : PortGraph V D} {a b c : V}
def darts : {a b : V}→Path Γ a b→List D
  | _,_,.nil _=>[]
  | _,_,.cons d p=>d::darts p
@[simp] lemma darts_nil (v : V) : darts (Path.nil (Γ:=Γ) v)=[] := rfl
@[simp] lemma darts_cons (d : D) (p : Path Γ (Γ.origin (Γ.reverse d)) b) :
    darts (.cons d p)=d::darts p := rfl
@[simp] lemma darts_cast {a b a' b' : V} (ha : a=a') (hb : b=b') (p : Path Γ a b) :
    darts (p.cast ha hb)=p.darts := by subst a';subst b';rfl
lemma darts_append (p : Path Γ a b) (q : Path Γ b c) :
    (p.append q).darts=p.darts++q.darts := by
  induction p with
  | nil=>rfl
  | cons d p ih=>simp only [append,darts_cons,ih,List.cons_append]
lemma darts_reverse (p : Path Γ a b) : p.reverse.darts=p.darts.reverse.map Γ.reverse := by
  induction p with
  | nil=>rfl
  | cons d p ih=>
    simp only [reverse] at ih
    simp only [reverse,darts_cast,darts_append,single,darts_cons,darts_nil,
      List.reverse_cons,List.map_append,List.map_cons,List.map_nil]
    exact congrArg (fun l=>l++[Γ.reverse d]) ih
lemma empty_ends (p : Path Γ a b) (he : p.darts=[]) : a=b := by
  cases p with
  | nil=>rfl
  | cons d p=>simp only [darts_cons,List.cons_ne_nil] at he
lemma first_origin (p : Path Γ a b) (hn : p.darts≠[]) : Γ.origin (p.darts.head hn)=a := by
  cases p with
  | nil=>exact False.elim (hn rfl)
  | cons d p=>rfl
lemma last_origin (p : Path Γ a b) (hn : p.darts≠[]) :
    Γ.origin (Γ.reverse (p.darts.getLast hn))=b := by
  induction p with
  | nil=>exact False.elim (hn rfl)
  | cons d p ih=>
    by_cases he : p.darts=[]
    · simpa only [darts_cons,he,List.getLast_singleton] using p.empty_ends he
    · simpa only [darts_cons,List.getLast_cons he] using ih he
lemma chain (p : Path Γ a b) : p.darts.IsChain (fun d e=>Γ.origin (Γ.reverse d)=Γ.origin e) := by
  induction p with
  | nil=>exact List.IsChain.nil
  | cons d p ih=>
    rw [darts_cons,List.isChain_cons]
    refine ⟨?_,ih⟩
    intro e he
    have hn : p.darts≠[] := by intro h;simp [h] at he
    have hh : e=p.darts.head hn := by
      exact (by simpa only [List.head?_eq_some_head hn,Option.mem_def,Option.some.injEq] using he : p.darts.head hn=e).symm
    rw [hh]
    exact (p.first_origin hn).symm
variable {A : Type*} (label : D→A×Bool)
def letters (p : Path Γ a b) : List (A×Bool) := p.darts.map label
lemma letters_mk (p : Path Γ a b) :
    FreeGroup.mk (p.letters label)=p.eval (fun d=>FreeGroup.mk [label d]) := by
  induction p with
  | nil=>rfl
  | cons d p ih=>
    change FreeGroup.mk (label d::p.letters label)=_
    rw [show label d::p.letters label=[label d]++p.letters label from rfl,←FreeGroup.mul_mk,ih]
    rfl
lemma letters_reverse (hl : ∀d,label (Γ.reverse d)=WordPairing.inverseLetter (label d))
    (p : Path Γ a b) : p.reverse.letters label=FreeGroup.invRev (p.letters label) := by
  simp only [letters,darts_reverse,List.map_map,FreeGroup.invRev,List.map_reverse]
  apply congrArg List.reverse
  apply List.map_congr_left
  intro d _
  exact hl d

end TorsionFreeZeroDivisors.GraphPresentation.Path
namespace TorsionFreeZeroDivisors.WordBlocks
open scoped Classical
variable {D A : Type*} (label : D→A)
def mapCoordinates : (ws : List (List D))→Occ ws≃Occ (ws.map (List.map label))
  | []=>Equiv.refl _
  | w::ws=>Equiv.sumCongr (finCongr (List.length_map (f:=label) (as:=w)).symm) (mapCoordinates ws)
lemma mapCoordinates_letter (ws : List (List D)) (x : Occ ws) :
    letter (ws.map (List.map label)) (mapCoordinates label ws x)=label (letter ws x) := by
  induction ws with
  | nil=>exact Empty.elim x
  | cons w ws ih=>
    cases x with
    | inl i=>exact List.getElem_map _
    | inr i=>exact ih i
lemma rotate_cast {n m : ℕ} (h : n=m) (i : Fin n) :
    finCongr h (finRotate n i)=finRotate m (finCongr h i) := by subst m;rfl
lemma mapCoordinates_rotation (ws : List (List D)) (x : Occ ws) :
    mapCoordinates label ws (BlockBoundary.rotation (lengths ws) x)=
      BlockBoundary.rotation (lengths (ws.map (List.map label))) (mapCoordinates label ws x) := by
  induction ws with
  | nil=>exact Empty.elim x
  | cons w ws ih=>
    cases x with
    | inl i=>exact congrArg Sum.inl (rotate_cast (List.length_map (f:=label) (as:=w)).symm i)
    | inr i=>exact congrArg Sum.inr (ih i)
/-- Actual boundary occurrences are graph darts; only their labels are inverse
matched. In particular, this does not silently require equal graph lifts. -/
structure LiftedMatching (inv : A→A) (ws : List (List D)) where
  partner : Equiv.Perm (Occ ws)
  involutive : Function.Involutive partner
  fixed_free : ∀x,partner x≠x
  compatible : ∀x,label (letter ws (partner x))=inv (label (letter ws x))
  genusZero : MapEuler.GenusZero (BlockBoundary.rotation (lengths ws)) partner
def Matching.lift {inv : A→A} {ws : List (List D)}
    (d : Matching inv (ws.map (List.map label))) : LiftedMatching label inv ws where
  partner := (mapCoordinates label ws).symm.permCongr d.partner
  involutive := PermutationTransport.involutive _ _ d.involutive
  fixed_free := PermutationTransport.fixed_free _ _ d.fixed_free
  compatible x := by
    rw [←mapCoordinates_letter label ws,←mapCoordinates_letter label ws]
    simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
    exact d.compatible (mapCoordinates label ws x)
  genusZero := by
    have hh := MapConjugation.genusZero (mapCoordinates label ws).symm _ _ d.genusZero
    have he : (mapCoordinates label ws).symm.permCongr
        (BlockBoundary.rotation (lengths (ws.map (List.map label))))=BlockBoundary.rotation (lengths ws) := by
      apply Equiv.ext
      intro x
      apply (mapCoordinates label ws).injective
      simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
      exact (mapCoordinates_rotation label ws x).symm
    rwa [he] at hh

end TorsionFreeZeroDivisors.WordBlocks
namespace TorsionFreeZeroDivisors.MapDeletion
open scoped Classical
open DeleteCycle MapEuler PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p)
lemma genusZero_iff_delete (hs : σ p≠p) :
    GenusZero σ α ↔ GenusZero (rotation σ p) (partner α p ha) := by
  refine ⟨genusZero_delete σ α p ha hs,fun hz=>?_⟩
  have hv := bypass_count σ p hs
  have hf := bypass_count (α*σ) p (face_nonfixed σ α p ha hs)
  rw [bypass_mul σ p α ha] at hf
  have hc := Nat.card_congr (componentEquiv σ α p ha hs)
  have he := support_count α p ha
  simp only [←Nat.card_eq_fintype_card] at hv hf
  dsimp only [GenusZero] at hz ⊢
  change Nat.card (Cycle (rotation σ p))=Nat.card (Cycle σ) at hv
  change Nat.card (Cycle (partner α p ha*rotation σ p))=Nat.card (Cycle (α*σ)) at hf
  rw [←hv,←hf,hc]
  have hsup : ∀ (i j : Fintype (Rest p)) (d e : DecidableEq (Rest p)),
      @Equiv.Perm.support (Rest p) d i (partner α p ha) =
      @Equiv.Perm.support (Rest p) e j (partner α p ha) := by
    intro i j d e
    cases Subsingleton.elim i j
    cases Subsingleton.elim d e
    rfl
  convert hz using 1
  rw [←he]
  congr 1
  exact congrArg Finset.card (hsup _ _ _ _)
end TorsionFreeZeroDivisors.MapDeletion
namespace TorsionFreeZeroDivisors.MarkerInsertion
open scoped Classical
open DeleteCycle
variable {O : Type} (σ α : Equiv.Perm O) (p : O)
/-- Insert an unpaired marker immediately before p. -/
def rotation : Equiv.Perm (Option O) := Equiv.swap none (some p)*Equiv.optionCongr σ
def partner : Equiv.Perm (Option O) := Equiv.optionCongr α
@[simp] lemma rotation_none : rotation σ p none=some p := by simp [rotation,Equiv.Perm.mul_apply]
@[simp] lemma partner_none : partner α none=none := rfl
lemma rotation_some (x : O) (hx : σ x≠p) : rotation σ p (some x)=some (σ x) := by
  simp only [rotation,Equiv.Perm.mul_apply,Equiv.optionCongr_apply,Option.map_some]
  exact Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using hx)
lemma rotation_predecessor : rotation σ p (some (σ.symm p))=none := by
  simp [rotation,Equiv.Perm.mul_apply]
lemma rotation_nonfixed : rotation σ p none≠none := by rw [rotation_none];exact Option.some_ne_none p
lemma partner_involutive (hi : Function.Involutive α) : Function.Involutive (partner α) := by
  intro x
  cases x with
  | none=>rfl
  | some x=>exact congrArg some (hi x)
lemma fixed_only (hf : ∀ x,α x≠x) (x : Option O) (hx : partner α x=x) : x=none := by
  cases x with
  | none=>rfl
  | some x=>exact False.elim (hf x (Option.some.inj hx))
def coordinates : O≃Rest (none : Option O) where
  toFun x := ⟨some x,Option.some_ne_none x⟩
  invFun x := x.val.get (Option.isSome_iff_ne_none.mpr x.property)
  left_inv _ := rfl
  right_inv _ := Subtype.ext (Option.some_get _)
variable [Fintype O]
lemma boundary_commutes (x : O) : bypass (rotation σ p) none (coordinates x)=coordinates (σ x) := by
  apply Subtype.ext
  rw [bypass_apply]
  simp only [coordinates,Equiv.coe_fn_mk,rotation_none]
  by_cases hx : σ x=p <;> simp [rotation,Equiv.Perm.mul_apply,Equiv.swap_apply_def,hx]
omit [Fintype O] in
lemma partner_commutes (x : O) : restrict (partner α) none (partner_none α) (coordinates x)=coordinates (α x) := rfl
lemma boundary_conjugate : bypass (rotation σ p) none=coordinates.permCongr σ := by
  apply Equiv.ext
  intro x
  obtain ⟨x,rfl⟩ := coordinates.surjective x
  rw [boundary_commutes]
  simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]
omit [Fintype O] in
lemma partner_conjugate : restrict (partner α) none (partner_none α)=coordinates.permCongr α := by
  apply Equiv.ext
  intro x
  obtain ⟨x,rfl⟩ := coordinates.surjective x
  rw [partner_commutes]
  simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]
/-- The literal marked rotation retains the exact genus-zero certificate.
This is only finite permutation insertion, not a surface realization. -/
theorem genusZero (hz : MapEuler.GenusZero σ α) : MapEuler.GenusZero (rotation σ p) (partner α) := by
  apply (MapDeletion.genusZero_iff_delete (rotation σ p) (partner α) none (partner_none α) (rotation_nonfixed σ p)).mpr
  unfold MapDeletion.rotation MapDeletion.partner
  rw [boundary_conjugate,partner_conjugate]
  have hh := MapConjugation.genusZero coordinates σ α hz
  convert hh using 1

end TorsionFreeZeroDivisors.MarkerInsertion
namespace TorsionFreeZeroDivisors.FinitePicture
open scoped Classical
open PortSubdivision
variable {V D A O : Type} [Fintype O] (Γ : PortGraph V D) (label : D→A) (inv : A→A) (x y : V)
  (σ α : Equiv.Perm O) (hi : Function.Involutive α) (hf : ∀i,α i≠i)
  (edge : O→D) (p : O)
  (hc : ∀i,label (edge (α i))=inv (label (edge i)))
  (hj : ∀i,σ i≠p → Γ.origin (Γ.reverse (edge i))=Γ.origin (edge (σ i)))
  (hp : Γ.origin (edge p)=x)
  (he : ∀i,σ i=p → Γ.origin (Γ.reverse (edge i))=y)
  (hz : MapEuler.GenusZero σ α)
/-- Insert the literal root break in a lifted genus-zero full matching. This
retains every graph dart and all endpoints; no graph path is replaced by its
rose label. The initial existence of this full matching must still be proved. -/
def ofBoundary : Data (O:=Option O) Γ label inv x y where
  rotation := MarkerInsertion.rotation σ p
  partner := MarkerInsertion.partner α
  involutive := MarkerInsertion.partner_involutive α hi
  marker := none
  marker_fixed := rfl
  fixed_only := MarkerInsertion.fixed_only α hf
  dart := Option.map edge
  none_iff i := by cases i <;> simp
  before i := i.elim y (fun j=>Γ.origin (edge j))
  after i := i.elim x (fun j=>Γ.origin (Γ.reverse (edge j)))
  begins i d hd := by
    cases i with
    | none=>simp at hd
    | some i=>exact congrArg Γ.origin (Option.some.inj hd)
  ends i d hd := by
    cases i with
    | none=>simp at hd
    | some i=>exact congrArg (Γ.origin ∘ Γ.reverse) (Option.some.inj hd)
  marker_before := rfl
  marker_after := rfl
  consistent i := by
    cases i with
    | none=>simpa only [MarkerInsertion.rotation_none,Option.elim_none,Option.elim_some] using hp.symm
    | some i=>
      by_cases hi : σ i=p
      · have hx : i=σ.symm p := σ.injective (hi.trans (σ.apply_symm_apply p).symm)
        rw [hx,MarkerInsertion.rotation_predecessor]
        exact he _ (σ.apply_symm_apply p)
      · rw [MarkerInsertion.rotation_some σ p i hi]
        exact hj i hi
  compatible i := by
    cases i with
    | none=>rfl
    | some i=>exact congrArg some (hc i)
  genusZero := MarkerInsertion.genusZero σ α p hz

end TorsionFreeZeroDivisors.FinitePicture

end

end OAI
