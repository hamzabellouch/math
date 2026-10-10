import Mathlib
import OAI.Algebra.GroupRing.AlgebraicPictures

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.GraphPresentation.Path
open PortSubdivision
variable {V D : Type} {Γ : PortGraph V D} {a b : V}
lemma join_rotation (p : Path Γ a b) (i : Fin p.darts.length)
    (hn : (finRotate p.darts.length i).val≠0) :
    Γ.origin (Γ.reverse (p.darts.get i))=Γ.origin (p.darts.get (finRotate p.darts.length i)) := by
  have hi : i.val+1≠p.darts.length := by
    intro he
    apply hn
    rw [ContiguousSplit.rotate_val,ite_eq_left he]
  have hin : i.val+1<p.darts.length := by omega
  have hj := (List.isChain_iff_getElem.mp p.chain) i.val hin
  simpa only [List.get_eq_getElem,ContiguousSplit.rotate_val,ite_eq_right hi] using hj
lemma end_rotation (p : Path Γ a b) (i : Fin p.darts.length)
    (hz : (finRotate p.darts.length i).val=0) :
    Γ.origin (Γ.reverse (p.darts.get i))=b := by
  have hi : i.val+1=p.darts.length := by
    rw [ContiguousSplit.rotate_val] at hz
    split_ifs at hz with h
    exact h
  have hn : p.darts≠[] := List.length_pos_iff.mp (by omega)
  have he : i.val=p.darts.length-1 := by omega
  simpa only [List.getLast_eq_getElem,List.get_eq_getElem,he] using p.last_origin hn
lemma first_get (p : Path Γ a b) (hn : 0<p.darts.length) : Γ.origin (p.darts.get ⟨0,hn⟩)=a := by
  simpa only [List.head_eq_getElem,List.get_eq_getElem] using p.first_origin (List.length_pos_iff.mp hn)
lemma closed_rotation (p : Path Γ a a) (i : Fin p.darts.length) :
    Γ.origin (Γ.reverse (p.darts.get i))=Γ.origin (p.darts.get (finRotate p.darts.length i)) := by
  by_cases hi : (finRotate p.darts.length i).val=0
  · rw [p.end_rotation i hi]
    have he : finRotate p.darts.length i=⟨0,by omega⟩ := Fin.ext hi
    rw [he]
    exact (p.first_get _).symm
  · exact p.join_rotation i hi

end TorsionFreeZeroDivisors.GraphPresentation.Path
namespace TorsionFreeZeroDivisors.WordBlocks
open scoped Classical
open PortSubdivision GraphPresentation
variable {V D A : Type} (Γ : PortGraph V D) (label : D→A) (inv : A→A)
def AllClosed (ws : List (List D)) : Prop := ∀w∈ws,∃v,∃p : Path Γ v v,p.darts=w
lemma closed_consistent (ws : List (List D)) (hc : AllClosed Γ ws) (i : Occ ws) :
    Γ.origin (Γ.reverse (letter ws i))=Γ.origin (letter ws (BlockBoundary.rotation (lengths ws) i)) := by
  induction ws with
  | nil=>exact Empty.elim i
  | cons w ws ih=>
    cases i with
    | inl i=>
      obtain ⟨v,p,rfl⟩ := hc w (List.mem_cons_self)
      exact p.closed_rotation i
    | inr i=>exact ih (fun w hw=>hc w (List.mem_cons_of_mem _ hw)) i
variable {x y : V} (p : Path Γ x y) (hxy : x≠y) (ws : List (List D))
def root : Occ (p.darts::ws) := .inl ⟨0,List.length_pos_iff.mpr (fun h=>hxy (p.empty_ends h))⟩
lemma root_begin : Γ.origin (letter (p.darts::ws) (root Γ p hxy ws))=x := p.first_get _
lemma boundary_join (hc : AllClosed Γ ws) (i : Occ (p.darts::ws))
    (hi : BlockBoundary.rotation (lengths (p.darts::ws)) i≠root Γ p hxy ws) :
    Γ.origin (Γ.reverse (letter (p.darts::ws) i))=
      Γ.origin (letter (p.darts::ws) (BlockBoundary.rotation (lengths (p.darts::ws)) i)) := by
  cases i with
  | inl i=>
    exact p.join_rotation i (fun h=>hi (congrArg Sum.inl (Fin.ext h)))
  | inr i=>exact closed_consistent Γ ws hc i
lemma boundary_end (i : Occ (p.darts::ws))
    (hi : BlockBoundary.rotation (lengths (p.darts::ws)) i=root Γ p hxy ws) :
    Γ.origin (Γ.reverse (letter (p.darts::ws) i))=y := by
  cases i with
  | inl i=>exact p.end_rotation i (congrArg Fin.val (Sum.inl.inj hi))
  | inr i=>cases hi
/-- All endpoints are furnished by literal graph paths, not by equality of
labels. Inserting the single exterior marker gives an actual finite picture. -/
def LiftedMatching.picture (d : LiftedMatching label inv (p.darts::ws)) (hc : AllClosed Γ ws) :
    FinitePicture.Data (O:=Option (Occ (p.darts::ws))) Γ label inv x y :=
  FinitePicture.ofBoundary Γ label inv x y (BlockBoundary.rotation (lengths (p.darts::ws)))
    d.partner d.involutive d.fixed_free (letter (p.darts::ws)) (root Γ p hxy ws)
    d.compatible (boundary_join Γ p hxy ws hc) (root_begin Γ p hxy ws)
    (boundary_end Γ p hxy ws) d.genusZero

end TorsionFreeZeroDivisors.WordBlocks
namespace TorsionFreeZeroDivisors.AlgebraicPictures
variable {A I : Type*} (rel : I→List (A×Bool))
open FreeGroup
lemma quotient_direct_matching (outer : List (A×Bool))
    (h : PresentedGroup.mk (relations rel) (mk outer)=1) :
    ∃ts : List (Term (A:=A) (I:=I)),
      Nonempty (WordBlocks.Matching WordPairing.inverseLetter (outer::coreWords rel ts)) := by
  have hh : PresentedGroup.mk (relations rel) (mk (invRev outer))=1 := by
    rw [←inv_mk,_root_.map_inv,h,inv_one]
  obtain ⟨ts,⟨d⟩⟩ := quotient_core_matching rel (invRev outer) hh
  exact ⟨ts,⟨by simpa only [invRev_invRev] using d⟩⟩
end TorsionFreeZeroDivisors.AlgebraicPictures
namespace TorsionFreeZeroDivisors.InitialPicture
open scoped Classical
open PortSubdivision GraphPresentation AlgebraicPictures
variable {V D A I : Type} (Γ : PortGraph V D) (label : D→A×Bool)
  (hl : ∀d,label (Γ.reverse d)=WordPairing.inverseLetter (label d))
abbrev Loop := Σv,Path Γ v v
variable (rel : I→Loop Γ)
def relWords (i : I) : List (A×Bool) := (rel i).2.letters label
def signedLoop (t : Term (A:=A) (I:=I)) : Loop Γ :=
  if t.positive then rel t.index else ⟨(rel t.index).1,(rel t.index).2.reverse⟩
include hl in
lemma signedLoop_letters (t : Term (A:=A) (I:=I)) :
    (signedLoop Γ rel t).2.letters label=t.core (relWords Γ label rel) := by
  rcases t with ⟨i,b,c⟩
  cases b
  · exact Path.letters_reverse label hl _
  · rfl
def innerWords (ts : List (Term (A:=A) (I:=I))) : List (List D) :=
  ts.map (fun t=>(signedLoop Γ rel t).2.darts)
include hl in
lemma innerWords_labels (ts : List (Term (A:=A) (I:=I))) :
    (innerWords Γ rel ts).map (List.map label)=coreWords (relWords Γ label rel) ts := by
  simp only [innerWords,coreWords,List.map_map]
  apply List.map_congr_left
  intro t _
  exact signedLoop_letters Γ label hl rel t
lemma innerWords_closed (ts : List (Term (A:=A) (I:=I))) :
    WordBlocks.AllClosed Γ (innerWords Γ rel ts) := by
  intro w hw
  obtain ⟨t,_,rfl⟩ := List.mem_map.mp hw
  exact ⟨(signedLoop Γ rel t).1,(signedLoop Γ rel t).2,rfl⟩
variable {x y : V} (p : Path Γ x y)
include hl in
/-- Algebraic nullity produces an actual lifted full matching on the given
outer path and literal signed closed relators. Empty relators are allowed. -/
theorem lifted_matching (h : PresentedGroup.mk (relations (relWords Γ label rel))
      (FreeGroup.mk (p.letters label))=1) :
    ∃ts : List (Term (A:=A) (I:=I)),Nonempty
      (WordBlocks.LiftedMatching label WordPairing.inverseLetter (p.darts::innerWords Γ rel ts)) := by
  obtain ⟨ts,⟨d⟩⟩ := quotient_direct_matching (relWords Γ label rel) (p.letters label) h
  refine ⟨ts,⟨WordBlocks.Matching.lift label ?_⟩⟩
  simpa only [List.map_cons,innerWords_labels Γ label hl rel,Path.letters] using d
include hl in
/-- The initial finite marked certificate is derived from nullity in the
literal graph-loop presentation. No preexisting picture, surface map, or
asphericity hypothesis is assumed. -/
theorem exists_picture (hxy : x≠y)
    (h : PresentedGroup.mk (relations (relWords Γ label rel)) (FreeGroup.mk (p.letters label))=1) :
    ∃(O : Type) (_ : Fintype O),Nonempty
      (FinitePicture.Data (O:=O) Γ label WordPairing.inverseLetter x y) := by
  obtain ⟨ts,⟨d⟩⟩ := lifted_matching Γ label hl rel p h
  exact ⟨Option (WordBlocks.Occ (p.darts::innerWords Γ rel ts)),inferInstance,
    ⟨d.picture Γ label WordPairing.inverseLetter p hxy _ (innerWords_closed Γ rel ts)⟩⟩

end TorsionFreeZeroDivisors.InitialPicture

namespace TorsionFreeZeroDivisors.GraphPresentation

section
open PortSubdivision
open scoped Classical
variable {V D : Type} (Γ : PortGraph V D)
/-- A finite choice of routes from the same base on each graph component. -/
structure Routes where
  base : V→V
  same : ∀ d,base (Γ.origin d)=base (Γ.origin (Γ.reverse d))
  path : ∀ v,Path Γ (base v) v

variable {S : Type*} (letters : D→FreeGroup S) (R : Routes Γ)
def word (v : V) : FreeGroup S := (R.path v).eval letters
def relator (d : D) : FreeGroup S :=
  word Γ letters R (Γ.origin d)*letters d*(word Γ letters R (Γ.origin (Γ.reverse d)))⁻¹
def relations : Set (FreeGroup S) := Set.range (relator Γ letters R)
abbrev Group := PresentedGroup (relations Γ letters R)
def value (v : V) : Group Γ letters R := PresentedGroup.mk _ (word Γ letters R v)
def letter (d : D) : Group Γ letters R := PresentedGroup.mk _ (letters d)
lemma edge (d : D) : value Γ letters R (Γ.origin (Γ.reverse d))=
    value Γ letters R (Γ.origin d)*letter Γ letters R d := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (show relator Γ letters R d∈relations Γ letters R from ⟨d,rfl⟩)
  simpa only [value,letter,map_mul] using h.symm

/-- Every literal path has the source's path-order value, independently of
which route was chosen to define the finite fundamental-cycle presentation. -/
lemma path_value {a b : V} (p : Path Γ a b) :
    p.eval (letter Γ letters R)=(value Γ letters R a)⁻¹*value Γ letters R b := by
  induction p with
  | nil v => simp
  | cons d p ih =>
    rw [Path.eval_cons,ih,edge]
    group
lemma closed_value (a : V) (p : Path Γ a a) : p.eval (letter Γ letters R)=1 := by
  rw [path_value]
  simp

/-- Labels of all closed walks, exactly as in the cone presentation. -/
def loopLabels : Set (FreeGroup S) := {w | ∃ a,∃ p : Path Γ a a,p.eval letters=w}
lemma loopLabels_subset_closure :
    loopLabels Γ letters ⊆ Subgroup.normalClosure (relations Γ letters R) := by
  rintro w ⟨a,p,rfl⟩
  apply PresentedGroup.mk_eq_one_iff.mp
  rw [← Path.eval_map]
  exact closed_value Γ letters R a p

lemma relator_mem_loopLabels
    (hl : ∀ d,letters (Γ.reverse d)=(letters d)⁻¹) (d : D) :
    relator Γ letters R d∈loopLabels Γ letters := by
  let p := ((R.path (Γ.origin d)).append (Path.single (Γ:=Γ) d)).append
    (R.path (Γ.origin (Γ.reverse d))).reverse
  refine ⟨R.base (Γ.origin d),p.cast rfl (R.same d).symm,?_⟩
  simp only [Path.eval_cast,p,Path.eval_append,Path.eval_single,Path.eval_reverse letters hl]
  rfl

/-- The finite edge-route presentation has precisely the normal closure of
all labels of graph loops, not merely some chosen graph relations. -/
theorem normalClosure_eq_loops
    (hl : ∀ d,letters (Γ.reverse d)=(letters d)⁻¹) :
    Subgroup.normalClosure (relations Γ letters R)=Subgroup.normalClosure (loopLabels Γ letters) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_mono
    rintro w ⟨d,rfl⟩
    exact relator_mem_loopLabels Γ letters R hl d
  · exact Subgroup.normalClosure_le_normal (loopLabels_subset_closure Γ letters R)

instance [Finite S] [Finite D] : _root_.Group.IsFinitelyPresented (Group Γ letters R) := by
  have : Finite (relations Γ letters R) := Set.finite_range (relator Γ letters R) |>.to_subtype
  infer_instance

end

open scoped Classical
open PortSubdivision
variable {V D A : Type} (Γ : PortGraph V D) (label : D→A×Bool)
  (hl : ∀d,label (Γ.reverse d)=WordPairing.inverseLetter (label d)) (R : Routes Γ)
def loopPath (d : D) : InitialPicture.Loop Γ :=
  ⟨R.base (Γ.origin d),(((R.path (Γ.origin d)).append (Path.single (Γ:=Γ) d)).append
    (R.path (Γ.origin (Γ.reverse d))).reverse).cast rfl (R.same d).symm⟩
def roseLabel (d : D) : FreeGroup A := FreeGroup.mk [label d]
include hl in
lemma roseLabel_reverse (d : D) : roseLabel label (Γ.reverse d)=(roseLabel label d)⁻¹ := by
  simp only [roseLabel,hl,FreeGroup.inv_mk]
  rfl
include hl in
lemma loopPath_word (d : D) :
    FreeGroup.mk ((loopPath Γ R d).2.letters label)=relator Γ (roseLabel label) R d := by
  rw [Path.letters_mk]
  change (loopPath Γ R d).2.eval (roseLabel label)=_
  simp only [loopPath,Path.eval_cast,Path.eval_append,Path.eval_single,
    Path.eval_reverse (roseLabel label) (roseLabel_reverse Γ label hl)]
  rfl
include hl in
lemma loopPath_relations : AlgebraicPictures.relations (InitialPicture.relWords Γ label (loopPath Γ R))=
    relations Γ (roseLabel label) R := by
  unfold AlgebraicPictures.relations relations
  congr 1
  funext d
  exact loopPath_word Γ label hl R d
include hl in
/-- A null word in the finite EDGE-ROUTE presentation used for the main
construction has an initial literal lifted picture; no relators were enlarged
or replaced by assumed graph-loop relations. -/
theorem route_picture {x y : V} (p : Path Γ x y) (hxy : x≠y)
    (h : p.eval (letter Γ (roseLabel label) R)=1) :
    ∃(O : Type) (_ : Fintype O),Nonempty
      (FinitePicture.Data (O:=O) Γ label WordPairing.inverseLetter x y) := by
  apply InitialPicture.exists_picture Γ label hl (loopPath Γ R) p hxy
  rw [loopPath_relations Γ label hl R,Path.letters_mk]
  change PresentedGroup.mk (relations Γ (roseLabel label) R) (p.eval (roseLabel label))=1
  rw [←Path.eval_map]
  exact h

end TorsionFreeZeroDivisors.GraphPresentation
namespace TorsionFreeZeroDivisors.FinitePicture.Data
open scoped Classical
variable {V D A B O : Type} [Fintype O] {Γ : PortSubdivision.PortGraph V D}
  {label : D→A} {inv : A→A} {x y : V} (a : Data (O:=O) Γ label inv x y)
  (f : A→B) (label' : D→B) (inv' : B→B)
  (hl : ∀d,label' d=f (label d)) (hf : ∀t,f (inv t)=inv' (f t))
/-- Relabel the alphabet, retaining the actual graph dart and endpoint data.
This does not change the path, partner, rotation, or exterior marker. -/
def relabel : Data (O:=O) Γ label' inv' x y := {a with
  compatible := by
    intro i
    have h1 : label'=f∘label := funext hl
    have h2 : inv'∘label'=f∘(inv∘label) := by
      funext d
      simp only [Function.comp_apply,hl,hf]
    rw [h2,h1]
    simpa only [Option.map_map] using congrArg (Option.map f) (a.compatible i) }

end TorsionFreeZeroDivisors.FinitePicture.Data
namespace TorsionFreeZeroDivisors.GraphPresentation
open PortSubdivision
open scoped Classical
variable {V D : Type} (Γ : PortGraph V D)
namespace Path
variable {Γ}
def ofWalk : {a b : V} → (ShortClosure.simpleGraph Γ).Walk a b→Path Γ a b
  | _,_,.nil => .nil _
  | _,_,.cons h p =>
    ((Path.single (Γ:=Γ) (ShortClosure.edgeDart Γ h)).cast
      (ShortClosure.edgeDart_start Γ h) (ShortClosure.edgeDart_end Γ h)).append (ofWalk p)
end Path
def routes : Routes Γ where
  base v := (ShortClosure.simpleGraph Γ).connectedComponentMk v |>.out
  same d := congrArg Quot.out (SimpleGraph.ConnectedComponent.sound (ShortClosure.dart_reachable Γ d))
  path v := Path.ofWalk (Classical.choice (SimpleGraph.ConnectedComponent.eq.mp
    ((ShortClosure.simpleGraph Γ).connectedComponentMk v).out_eq))

end TorsionFreeZeroDivisors.GraphPresentation
namespace TorsionFreeZeroDivisors.ConcreteGroup

section
open scoped Classical BigOperators
open PortSubdivision TypedGraphs ConditionedMatchings SampleGraph
/-- The literal rose letters, with the fixed source inverse pairing. -/
def freeLetter (t : Types.Letter) : FreeGroup Types.Generator :=
  if (Types.signedLetter.symm t).2 then FreeGroup.of (Types.signedLetter.symm t).1
  else (FreeGroup.of (Types.signedLetter.symm t).1)⁻¹
lemma freeLetter_inverse (t : Types.Letter) :
    freeLetter (Types.inverse t)=(freeLetter t)⁻¹ := by
  obtain ⟨⟨g,b⟩,rfl⟩ := Types.signedLetter.surjective t
  cases b <;> simp [freeLetter]
variable (rep : ℕ) (r : ActualPatternEvent.Match rep)
abbrev Γ := SampleGraph.graph rep r
def labels : DA rep⊕DB rep → FreeGroup Types.Generator := freeLetter ∘ SampleGraph.label rep
lemma labels_reverse (d : DA rep⊕DB rep) : labels rep ((Γ rep r).reverse d)=(labels rep d)⁻¹ := by
  simp only [labels,Function.comp_apply,SampleGraph.label_reverse,freeLetter_inverse]
def routes := GraphPresentation.routes (Γ rep r)
abbrev G := GraphPresentation.Group (Γ rep r) (labels rep) (routes rep r)
def value : VA rep⊕VB rep → G rep r := GraphPresentation.value (Γ rep r) (labels rep) (routes rep r)
def letter (t : Types.Letter) : G rep r := PresentedGroup.mk _ (freeLetter t)
instance : Group.IsFinitelyPresented (G rep r) := inferInstance
lemma presentation_exact :
    Subgroup.normalClosure (GraphPresentation.relations (Γ rep r) (labels rep) (routes rep r))=
      Subgroup.normalClosure (GraphPresentation.loopLabels (Γ rep r) (labels rep)) :=
  GraphPresentation.normalClosure_eq_loops _ _ _ (labels_reverse rep r)
lemma edge (d : DA rep⊕DB rep) : value rep r ((Γ rep r).origin ((Γ rep r).reverse d))=
    value rep r ((Γ rep r).origin d)*letter rep r (SampleGraph.label rep d) :=
  GraphPresentation.edge _ _ _ d
lemma path_value {a b : VA rep⊕VB rep} (p : GraphPresentation.Path (Γ rep r) a b) :
    p.eval (letter rep r ∘ SampleGraph.label rep)=(value rep r a)⁻¹*value rep r b :=
  GraphPresentation.path_value _ _ _ p
end

open scoped Classical
open SampleGraph
lemma freeLetter_mk (t : Types.Letter) : freeLetter t=FreeGroup.mk [Types.signedLetter.symm t] := by
  obtain ⟨⟨g,b⟩,rfl⟩ := Types.signedLetter.surjective t
  cases b <;> simp [freeLetter, FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev]
variable {rep : ℕ} (r : ActualPatternEvent.Match rep)
lemma signed_label_reverse (d : DA rep⊕DB rep) :
    Types.signedLetter.symm (SampleGraph.label rep ((Γ rep r).reverse d))=
      WordPairing.inverseLetter (Types.signedLetter.symm (SampleGraph.label rep d)) := by
  rw [SampleGraph.label_reverse]
  simp [Types.inverse,WordPairing.inverseLetter]
lemma letter_signed (d : DA rep⊕DB rep) :
    GraphPresentation.roseLabel (Types.signedLetter.symm ∘ SampleGraph.label rep) d=labels rep d := by
  exact (freeLetter_mk _).symm
/-- A literal path null in the exact constructed group yields a reduced
finite marked disk picture on the original source alphabet and graph darts. -/
theorem reduced_picture {z w : VA rep⊕VB rep} (p : GraphPresentation.Path (Γ rep r) z w)
    (hzw : z≠w) (h : p.eval (letter rep r ∘ SampleGraph.label rep)=1) :
    ∃n,∃a : FinitePicture.Data (O:=Fin n) (Γ rep r) (SampleGraph.label rep) Types.inverse z w,
      a.Reduced := by
  have hlabels : GraphPresentation.roseLabel (Types.signedLetter.symm ∘ SampleGraph.label rep)=labels rep :=
    funext (letter_signed (rep:=rep))
  obtain ⟨O,hO,⟨a⟩⟩ := GraphPresentation.route_picture (Γ rep r)
    (Types.signedLetter.symm ∘ SampleGraph.label rep) (signed_label_reverse r) (routes rep r) p hzw (by
      rw [hlabels]
      exact h)
  let _ := hO
  let b := a.relabel Types.signedLetter (SampleGraph.label rep) Types.inverse
    (fun d=> (Types.signedLetter.apply_symm_apply _).symm) (by
      intro t
      exact (Types.inverse_signed t.1 t.2).symm)
  obtain ⟨n,_,c,hc⟩ := b.exists_reduced (by intro t; exact Types.inverse_inverse t)
    (SampleGraph.label_reverse rep r)
  exact ⟨n,c,hc⟩

end TorsionFreeZeroDivisors.ConcreteGroup

end

end OAI
