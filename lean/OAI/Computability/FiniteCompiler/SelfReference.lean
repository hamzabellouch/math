import OAI.Computability.FiniteCompiler.UniformPaths
import OAI.GroupTheory.BooneHigman.PartialAffine

namespace OAI

/-!
Controlled shorter-input evaluator calls, fixed points, totality, and tested-class realization.
-/

namespace FiniteAlgebraicEnvelopes.Bootstrap
namespace Projection
variable {A B : Type*}
def left (w : List (A ⊕ B)) : List A :=
  w.filterMap (fun a => match a with | .inl a => some a | .inr _ => none)
def right (w : List (A ⊕ B)) : List B :=
  w.filterMap (fun a => match a with | .inl _ => none | .inr b => some b)

@[simp] theorem left_append (u v : List (A ⊕ B)) : left (u++v)=left u++left v := List.filterMap_append
@[simp] theorem right_append (u v : List (A ⊕ B)) : right (u++v)=right u++right v := List.filterMap_append
 theorem left_length (w : List (A ⊕ B)) : (left w).length≤w.length := List.length_filterMap_le _ _
 theorem right_length (w : List (A ⊕ B)) : (right w).length≤w.length := List.length_filterMap_le _ _

variable [Primcodable A] [Primcodable B]
 theorem primrec_left : Primrec (left (A:=A) (B:=B)) := by
  have hh : Primrec (fun a : A ⊕ B => match a with | .inl a => some a | .inr _ => none) :=
    (Primrec.sumCasesOn Primrec.id (Primrec.option_some.comp Primrec.snd).to₂
      (Primrec.const none).to₂).of_eq (by intro a; cases a <;> rfl)
  exact Primrec.listFilterMap Primrec.id (hh.comp Primrec.snd).to₂
 theorem primrec_right : Primrec (right (A:=A) (B:=B)) := by
  have hh : Primrec (fun a : A ⊕ B => match a with | .inl _ => none | .inr b => some b) :=
    (Primrec.sumCasesOn Primrec.id (Primrec.const none).to₂
      (Primrec.option_some.comp Primrec.snd).to₂).of_eq (by intro a; cases a <;> rfl)
  exact Primrec.listFilterMap Primrec.id (hh.comp Primrec.snd).to₂
end Projection

namespace Tested
open Compiler Compiler.Simulator MachineRealization MachineRealization.ParameterCode
open scoped Compiler.HeadCodec

variable {S T Γ Q : Type*} [Fintype T] [Fintype Γ] [Fintype Q]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable T] [Primcodable Γ] [Primcodable Q]
variable (A : Alphabet S Γ) (M : Machine Q Γ) (p : S) (B : Alphabet T (Bool×Γ))

abbrev X (T Γ Q : Type*) := Word.Letter T (Bool×Γ) (ParameterCode.Control Q)
abbrev Y (T Γ Q : Type*) := X T Γ Q ⊕ PartialAffine.Letter
abbrev Class (T Γ Q : Type*) := List (X T Γ Q) × List PartialAffine.Letter

def combine (q : Class T Γ Q) : Option (Class T Γ Q) :=
  if q.1=[.zero] then none else some q

omit [Fintype Q] [Primcodable T] [Primcodable Γ] in
 theorem primrec_combine : Primrec (combine (T:=T) (Γ:=Γ) (Q:=Q)) := by
  let : DecidablePred (fun q : Class T Γ Q => q.1=([Path.Letter.zero] : List (X T Γ Q))) :=
    fun _ => inferInstance
  have hp : PrimrecPred (fun q : Class T Γ Q => q.1=([Path.Letter.zero] : List (X T Γ Q))) :=
    Primrec.eq.comp Primrec.fst (Primrec.const _)
  exact Primrec.ite hp (Primrec.const none) (Primrec.option_some.comp Primrec.id)

/-- The literal tested class from the self-reference construction: zero precisely for the compiler
    zero output, and otherwise the compiler word together with a canonical,
    decidable coding of the actual auxiliary partial affine map. -/
noncomputable def family (f : ℕ × List T → Part (List T)) (n : ℕ) (w : List (Y T Γ Q)) :
    Part (Option (Class T Γ Q)) :=
  (codedNormal A M p B f (n,Projection.left w)).map
    (fun o => combine (o,PartialAffine.testedClass (Projection.right w)))

 theorem partrec_family {f : ℕ × List T → Part (List T)} (hf : Partrec f) :
    Partrec₂ (family A M p B f) := by
  have hh : Partrec (fun x : ℕ × List (Y T Γ Q) =>
      codedNormal A M p B f (x.1,Projection.left x.2)) :=
    (partrec_codedNormal A M p B hf).comp
    (Computable.fst.pair ((Projection.primrec_left (A:=X T Γ Q) (B:=PartialAffine.Letter)).to_comp.comp Computable.snd))
  exact (hh.map (primrec_combine.to_comp.comp
    (Computable.snd.pair (PartialAffine.computable_testedClass.comp
      (Projection.primrec_right.to_comp.comp (Computable.snd.comp Computable.fst))))).to₂).to₂

noncomputable def letters (n : ℕ) : List (Y T Γ Q) :=
  (ParameterCode.letters (T:=T) (Γ:=Γ) (Q:=Q) n).map Sum.inl ++
    (Static.letters PartialAffine.Letter).map Sum.inr

omit [DecidableEq T] [DecidableEq Γ] [DecidableEq Q] [Primcodable T] [Primcodable Γ] in
 theorem primrec_letters : Primrec (letters (T:=T) (Γ:=Γ) (Q:=Q)) :=
  Primrec.list_append.comp (Primrec.list_map ParameterCode.primrec_letters
    (Primrec.sumInl.comp Primrec.snd).to₂) (Primrec.const _)

omit [Primcodable T] [Primcodable Γ] in
 theorem family_mem {f : ℕ × List T → Part (List T)} {n : ℕ} {w : List (Y T Γ Q)}
    {o : List (X T Γ Q)} (ho : o∈codedNormal A M p B f (n,Projection.left w)) :
    combine (o,PartialAffine.testedClass (Projection.right w))∈family A M p B f n w :=
  Part.mem_map _ ho

end Tested
end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes.Bootstrap.Uniform

section
variable {A B S : Type*} [DecidableEq A]

def tail (a c : S) (ls : List A) (x : A) : List S :=
  List.replicate (ls.idxOf x) a ++ c :: List.replicate (ls.length+1-ls.idxOf x) a

def encode (b a c : S) (ls : List A) (w : List A) : List S :=
  w.flatMap (fun x => b :: tail a c ls x)

 theorem tail_length (a c : S) (ls : List A) (x : A) :
    (tail a c ls x).length=ls.length+2 := by
  have h := List.idxOf_le_length (a := x) (l := ls)
  simp only [tail,List.length_append,List.length_replicate,List.length_cons]
  omega

 theorem code_length (b a c : S) (ls : List A) (w : List A) :
    (encode b a c ls w).length=(ls.length+3)*w.length := by
  induction w with
  | nil => simp [encode]
  | cons x w ih =>
    simp only [encode,List.flatMap_cons,List.length_append,List.length_cons,tail_length] at *
    simp only [Nat.mul_add, Nat.mul_one]
    omega

/-- A genuine block code on any finite alphabet injected into the displayed
support. No choice of an enumeration at the parameter is used. -/
def localCode [DecidableEq S] (b a c : S) (hba : b≠a) (hbc : b≠c) (hac : a≠c)
    (ls : List A) (i : B → A) (hi : Function.Injective i) (hm : ∀ x,i x∈ls) : BlockCode B S where
  marker := b
  tail x := tail a c ls (i x)
  width := ls.length+2
  tail_length x := tail_length a c ls (i x)
  tail_avoids x := by simp [tail,hba,hbc]
  injective := by
    intro x y he
    apply hi
    apply (List.idxOf_inj (hm x)).mp
    have he' : binaryTail a c ls.length ⟨ls.idxOf (i x),List.idxOf_lt_length_of_mem (hm x)⟩ =
        binaryTail a c ls.length ⟨ls.idxOf (i y),List.idxOf_lt_length_of_mem (hm y)⟩ := he
    exact congrArg Fin.val (binaryTail_injective hac ls.length he')

 theorem localCode_encode [DecidableEq S] (b a c : S) (hba : b≠a) (hbc : b≠c) (hac : a≠c)
    (ls : List A) (i : B → A) (hi : Function.Injective i) (hm : ∀ x,i x∈ls) (w : List B) :
    (localCode b a c hba hbc hac ls i hi hm).encode w=encode b a c ls (w.map i) := by
  simp only [BlockCode.encode,localCode,encode,List.flatMap_map]
  rfl

variable [Primcodable A] [Primcodable S]
 theorem primrec_tail (a c : S) : Primrec₂ (tail a c (A := A)) := by
  have hi : Primrec (fun p : List A × A => p.1.idxOf p.2) :=
    Primrec.list_idxOf.comp Primrec.snd Primrec.fst
  exact (Primrec.list_append.comp ((Selectors.primrec_replicate a).comp hi)
    (Primrec.list_cons.comp (Primrec.const c) ((Selectors.primrec_replicate a).comp
      (Primrec.nat_sub.comp (Primrec.succ.comp (Primrec.list_length.comp Primrec.fst)) hi)))).to₂

 theorem primrec_encode (b a c : S) : Primrec₂ (encode b a c (A := A)) := by
  exact (Primrec.list_flatMap Primrec.snd
    (Primrec.list_cons.comp (Primrec.const b)
      ((primrec_tail a c).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂).to₂

end

section
variable {P A S Q : Type*} [DecidableEq A] [DecidableEq S] [DecidableEq Q]

def pickStep (lt : List A → List A → Bool) (q : Option Q) (best : List A)
    (v : List A × Option Q) : List A :=
  if v.2=q ∧ lt v.1 best=true then v.1 else best

def pick (lt : List A → List A → Bool) (ps : List (List A × Option Q))
    (w : List A) (q : Option Q) : List A := ps.foldl (pickStep lt q) w

def output (code : List A → List S) (lt : List A → List A → Bool) (z : S)
    (ps : List (List A × Option Q)) (v : List A × Option Q) : List S :=
  if v.2=none then [z] else code (pick lt ps v.1 v.2)

def table (code : List A → List S) (lt : List A → List A → Bool) (z : S)
    (ps : List (List A × Option Q)) : List (List S × List S) :=
  ps.flatMap fun v => if v.1≠[] ∧ output code lt z ps v≠code v.1 then
    [(code v.1,output code lt z ps v)] else []

def compute (ls : List A) (code : List A → List S) (lt : List A → List A → Bool)
    (z : S) (f : List A → Part (Option Q)) (n : ℕ) : Part (List (List S × List S)) :=
  (Effect.traverse (fun w => (f w).map (w,·)) (words ls n)).map (table code lt z)

section Computability
variable [Primcodable P] [Primcodable A] [Primcodable S] [Primcodable Q]
  (code : P → List A → List S) (lt : P → List A → List A → Bool) (z : S)
  (hc : Primrec₂ code) (hl : Primrec (fun x : P × List A × List A => lt x.1 x.2.1 x.2.2))
variable {X : Type*} [Primcodable X]

omit [DecidableEq A] in
include hl in
 theorem primrec_pickStep {p : X → P} {q : X → Option Q} {best : X → List A}
    {v : X → List A × Option Q} (hp : Primrec p) (hq : Primrec q)
    (hb : Primrec best) (hv : Primrec v) :
    Primrec (fun x => pickStep (lt (p x)) (q x) (best x) (v x)) :=
  Primrec.ite ((Primrec.eq.comp (Primrec.snd.comp hv) hq).and
    (Primrec.eq.comp (hl.comp (hp.pair ((Primrec.fst.comp hv).pair hb))) (Primrec.const true)))
    (Primrec.fst.comp hv) hb

omit [DecidableEq A] in
include hl in
 theorem primrec_pick {p : X → P} {q : X → Option Q} {w : X → List A}
    {ps : X → List (List A × Option Q)} (hp : Primrec p) (hq : Primrec q)
    (hw : Primrec w) (hps : Primrec ps) :
    Primrec (fun x => pick (lt (p x)) (ps x) (w x) (q x)) :=
  Primrec.list_foldl hps hw (primrec_pickStep lt hl (hp.comp Primrec.fst)
    (hq.comp Primrec.fst) (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

omit [DecidableEq A] [DecidableEq S] in
include hc hl in
 theorem primrec_output : Primrec (fun x : P × List (List A × Option Q) × (List A × Option Q) =>
    output (code x.1) (lt x.1) z x.2.1 x.2.2) := by
  have hv : Primrec (fun x : P × List (List A × Option Q) × (List A × Option Q) => x.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact Primrec.ite (Primrec.eq.comp (Primrec.snd.comp hv) (Primrec.const none))
    (Primrec.const [z]) (hc.comp Primrec.fst (primrec_pick lt hl Primrec.fst
      (Primrec.snd.comp hv) (Primrec.fst.comp hv) (Primrec.fst.comp Primrec.snd)))

omit [DecidableEq A] in
include hc hl in
 theorem primrec_table : Primrec (fun x : P × List (List A × Option Q) => table (code x.1) (lt x.1) z x.2) := by
  apply Primrec.list_flatMap Primrec.snd
  have hp : Primrec (fun x : (P × List (List A × Option Q)) × (List A × Option Q) => x.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hout := (primrec_output code lt z hc hl).comp
    (hp.pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
  have hcode := hc.comp hp (Primrec.fst.comp Primrec.snd)
  exact (Primrec.ite ((Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const [])).not.and
    (Primrec.eq.comp hout hcode).not)
    (Primrec.list_cons.comp (hcode.pair hout) (Primrec.const [])) (Primrec.const [])).to₂

omit [DecidableEq A] in
include hc hl in
 theorem partrec_compute {ls : P → List A} (hs : Primrec ls)
    {f : P → List A → Part (Option Q)} (hf : Partrec₂ f) :
    Partrec₂ (fun p => compute (ls p) (code p) (lt p) z (f p)) := by
  have hp : Partrec₂ (fun p w => (f p w).map (w,·)) :=
    (hf.map ((Computable.snd.comp Computable.fst).pair Computable.snd).to₂).to₂
  have hw : Primrec (fun x : P × ℕ => words (ls x.1) x.2) :=
    Uniform.primrec_words.comp (hs.comp Primrec.fst) Primrec.snd
  exact (((Effect.partrec_traverse_parameter hp).comp Computable.fst hw.to_comp).map
    ((primrec_table code lt z hc hl).to_comp.comp
      ((Computable.fst.comp Computable.fst).pair Computable.snd)).to₂).to₂
end Computability

omit [DecidableEq A] in
 theorem compute_specialize [Fintype A] {r : A → A → Prop} [DecidableRel (List.Shortlex r)]
    (C : BlockCode A S) (z : S) (f : List A → Part (Option Q)) (n : ℕ) :
    compute (Static.letters A) C.encode (fun u v => decide (List.Shortlex r u v)) z f n =
      Search.compute (r := r) C z f n := by
  have hp : pickStep (Q := Q) (fun u v => decide (List.Shortlex r u v))=Canonical.pickStep (r := r) := by
    funext q w v
    simp only [pickStep,Canonical.pickStep,decide_eq_true_eq]
  have ht : table (Q := Q) C.encode (fun u v => decide (List.Shortlex r u v)) z = Search.table (r := r) C z := by
    funext ps
    simp only [table,Search.table,output,Search.output,pick,Canonical.pick,hp]
    rfl
  simp only [compute,words_specialize,Search.compute,ht]

end

variable {P S A B Q R : Type*} [Primcodable S] [Fintype S]
  [DecidableEq S] [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]

noncomputable def bases (z : S) (ls : List A) (ms : List B)
    (code : List A → List S) (code' : List B → List S)
    (lt : List A → List A → Bool) (lt' : List B → List B → Bool)
    (d e : ℕ) (f : List A → Part (Option Q)) (g : List B → Part (Option R)) (n : ℕ) :
    Part (List (List S × List S)) :=
  (compute ls code lt z f (n/d)).bind fun rc =>
    (compute ms code' lt' z g (n/e)).map fun rd => Base.absorption z ++ rc ++ rd

noncomputable def tables (a : Selectors.Markers S) (ls : List A) (ms : List B)
    (code : List A → List S) (code' : List B → List S)
    (lt : List A → List A → Bool) (lt' : List B → List B → Bool)
    (d e : ℕ) (f : List A → Part (Option Q)) (g : List B → Part (Option R)) (n : ℕ) :
    Part (List (List S × List S)) :=
  (bases a.zero ls ms code code' lt lt' d e f g n).map fun b =>
    Selectors.process (a:=a) b (Selectors.stages a.zero) n n

section Computability
variable [Primcodable P] [Primcodable A] [Primcodable B] [Primcodable Q] [Primcodable R]
variable (a : Selectors.Markers S) (ls : P → List A) (ms : P → List B)
    (code : P → List A → List S) (code' : P → List B → List S)
    (lt : P → List A → List A → Bool) (lt' : P → List B → List B → Bool)
    (d e : P → ℕ) (f : P → List A → Part (Option Q)) (g : P → List B → Part (Option R))
variable (hls : Primrec ls) (hms : Primrec ms) (hc : Primrec₂ code) (hc' : Primrec₂ code')
    (hlt : Primrec (fun x : P × List A × List A => lt x.1 x.2.1 x.2.2))
    (hlt' : Primrec (fun x : P × List B × List B => lt' x.1 x.2.1 x.2.2))
    (hd : Primrec d) (he : Primrec e) (hf : Partrec₂ f) (hg : Partrec₂ g)
include hls hms hc hc' hlt hlt' hd he hf hg in
omit [DecidableEq A] [DecidableEq B] in
 theorem partrec_bases : Partrec₂ (fun p => bases a.zero (ls p) (ms p) (code p) (code' p)
    (lt p) (lt' p) (d p) (e p) (f p) (g p)) := by
  have h1 : Partrec (fun x : P × ℕ => compute (ls x.1) (code x.1) (lt x.1) a.zero (f x.1) (x.2/d x.1)) :=
    (partrec_compute code lt a.zero hc hlt hls hf).comp Computable.fst
      (Primrec.nat_div.to_comp.comp Computable.snd (hd.to_comp.comp Computable.fst))
  have h2 : Partrec (fun x : (P × ℕ) × List (List S × List S) =>
        compute (ms x.1.1) (code' x.1.1) (lt' x.1.1) a.zero (g x.1.1) (x.1.2/e x.1.1)) :=
    (partrec_compute code' lt' a.zero hc' hlt' hms hg).comp (Computable.fst.comp Computable.fst)
      (Primrec.nat_div.to_comp.comp (Computable.snd.comp Computable.fst)
        (he.to_comp.comp (Computable.fst.comp Computable.fst)))
  exact (h1.bind (h2.map (Primrec.list_append.to_comp.comp
    (Primrec.list_append.to_comp.comp (Computable.const (Base.absorption a.zero))
      (Computable.snd.comp Computable.fst)) Computable.snd).to₂).to₂).to₂

include hls hms hc hc' hlt hlt' hd he hf hg in
omit [DecidableEq A] [DecidableEq B] in
 theorem partrec_tables : Partrec₂ (fun p => tables a (ls p) (ms p) (code p) (code' p)
    (lt p) (lt' p) (d p) (e p) (f p) (g p)) := by
  have hb := partrec_bases a ls ms code code' lt lt' d e f g hls hms hc hc' hlt hlt' hd he hf hg
  exact (hb.map ((Selectors.primrec_process a _ (Selectors.primrec_stages a.zero)).to_comp.comp
    (Computable.snd.pair (Computable.snd.comp Computable.fst))
    (Computable.snd.comp Computable.fst)).to₂).to₂
end Computability

omit [DecidableEq A] [DecidableEq B] in
 theorem tables_specialize [Fintype A] [Fintype B]
    {r : A → A → Prop} {s : B → B → Prop} [DecidableRel (List.Shortlex r)] [DecidableRel (List.Shortlex s)]
    (a : Selectors.Markers S) (C : BlockCode A S) (D : BlockCode B S)
    (f : List A → Part (Option Q)) (g : List B → Part (Option R)) (n : ℕ) :
    tables a (Static.letters A) (Static.letters B) C.encode D.encode
      (fun u v => decide (List.Shortlex r u v)) (fun u v => decide (List.Shortlex s u v))
      (C.width+1) (D.width+1) f g n=Build.tables (r:=r) (s:=s) a C D f g n := by
  simp only [tables,bases,Build.tables,Build.bases,compute_specialize]

end FiniteAlgebraicEnvelopes.Bootstrap.Uniform

namespace FiniteAlgebraicEnvelopes.Bootstrap.LexBinary
variable {A B S : Type*}

/-- Binary tails in their literal lexicographic order, with `a` before `c`. -/
def words (a c : S) : ℕ → List (List S)
  | 0 => [[]]
  | n+1 => (words a c n).map (a::·) ++ (words a c n).map (c::·)

 theorem length_words (a c : S) (n : ℕ) : (words a c n).length=2^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [words,ih,pow_succ,Nat.mul_two]

 theorem mem_length {a c : S} {n : ℕ} {w : List S} (h : w∈words a c n) : w.length=n := by
  induction n generalizing w with
  | zero => simpa [words] using h
  | succ n ih =>
    simp only [words,List.mem_append,List.mem_map] at h
    rcases h with ⟨u,hu,rfl⟩ | ⟨u,hu,rfl⟩ <;> simp [ih hu]

 theorem mem_letters {a c s : S} {n : ℕ} {w : List S} (h : w∈words a c n) (hs : s∈w) : s=a ∨ s=c := by
  induction n generalizing w with
  | zero => simp [words] at h; subst w; cases hs
  | succ n ih =>
    simp only [words,List.mem_append,List.mem_map] at h
    rcases h with ⟨u,hu,rfl⟩ | ⟨u,hu,rfl⟩
    · rcases List.mem_cons.mp hs with rfl | hs
      · exact Or.inl rfl
      · exact ih hu hs
    · rcases List.mem_cons.mp hs with rfl | hs
      · exact Or.inr rfl
      · exact ih hu hs

 theorem nodup {a c : S} (hac : a≠c) (n : ℕ) : (words a c n).Nodup := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    rw [words,List.nodup_append]
    refine ⟨ih.map (by intro u v h; exact (List.cons.inj h).2),
      ih.map (by intro u v h; exact (List.cons.inj h).2),?_⟩
    intro u hu v hv he
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hu
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hv
    exact hac (List.cons.inj he).1

 theorem ordered {r : S → S → Prop} {a c : S} (hac : r a c) (n : ℕ) :
    (words a c n).Pairwise (List.Lex r) := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    rw [words,List.pairwise_append]
    refine ⟨?_,?_,?_⟩
    · rw [List.pairwise_map]; exact ih.imp (fun h => List.Lex.cons h)
    · rw [List.pairwise_map]; exact ih.imp (fun h => List.Lex.cons h)
    · intro u hu v hv
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp hu
      obtain ⟨y,_,rfl⟩ := List.mem_map.mp hv
      exact List.Lex.rel hac

variable [DecidableEq A]
def tail (a c : S) (d : ℕ) (ls : List A) (x : A) : List S :=
  (words a c d).getD (ls.idxOf x) []

def encode (b a c : S) (d : ℕ) (ls : List A) (w : List A) : List S :=
  w.flatMap (fun x => b :: tail a c d ls x)

 theorem index_bound {firstSymbol secondSymbol : S} (d : ℕ) (ls : List A)
    (hls : ls.length≤2^d) {x : A} (hx : x∈ls) :
    ls.idxOf x < (words firstSymbol secondSymbol d).length := by
  rw [length_words]
  exact (List.idxOf_lt_length_of_mem hx).trans_le hls

variable [DecidableEq S]
def code (b a c : S) (hba : b≠a) (hbc : b≠c) (hac : a≠c)
    (d : ℕ) (ls : List A) (hls : ls.length≤2^d)
    (i : B → A) (hi : Function.Injective i) (hm : ∀ x,i x∈ls) : BlockCode B S where
  marker := b
  tail x := tail a c d ls (i x)
  width := d
  tail_length x := by
    rw [tail,List.getD_eq_getElem _ _ (index_bound d ls hls (hm x))]
    exact mem_length (List.getElem_mem _)
  tail_avoids x := by
    rw [tail,List.getD_eq_getElem _ _ (index_bound d ls hls (hm x))]
    intro hb
    rcases mem_letters (List.getElem_mem _) hb with h | h
    · exact hba h
    · exact hbc h
  injective := by
    intro x y h
    apply hi
    apply (List.idxOf_inj (hm x)).mp
    simp only [tail] at h
    rw [List.getD_eq_getElem _ _ (index_bound d ls hls (hm x)),
      List.getD_eq_getElem _ _ (index_bound d ls hls (hm y))] at h
    exact (nodup hac d).getElem_inj_iff.mp h

omit [DecidableEq S] in
 theorem code_encode (b a c : S) (hba : b≠a) (hbc : b≠c) (hac : a≠c)
    (d : ℕ) (ls : List A) (hls : ls.length≤2^d)
    (i : B → A) (hi : Function.Injective i) (hm : ∀ x,i x∈ls) (w : List B) :
    (code b a c hba hbc hac d ls hls i hi hm).encode w=encode b a c d ls (w.map i) := by
  simp only [BlockCode.encode,code,encode,List.flatMap_map]
  rfl

omit [DecidableEq S] in
 theorem code_order {r : S → S → Prop} (b a c : S) (hba : b≠a) (hbc : b≠c) (hac : a≠c)
    (hr : r a c) (d : ℕ) (ls : List A) (hls : ls.length≤2^d)
    (i : B → A) (hi : Function.Injective i) (hm : ∀ x,i x∈ls) {x y : B}
    (hxy : ls.idxOf (i x)<ls.idxOf (i y)) :
    List.Lex r ((code b a c hba hbc hac d ls hls i hi hm).block x)
      ((code b a c hba hbc hac d ls hls i hi hm).block y) := by
  apply List.Lex.cons
  change List.Lex r (tail a c d ls (i x)) (tail a c d ls (i y))
  rw [tail,tail,List.getD_eq_get _ _ ⟨_,index_bound d ls hls (hm x)⟩,
    List.getD_eq_get _ _ ⟨_,index_bound d ls hls (hm y)⟩]
  exact (ordered hr d).rel_get_of_lt (a := ⟨_,index_bound d ls hls (hm x)⟩)
    (b := ⟨_,index_bound d ls hls (hm y)⟩) hxy

omit [DecidableEq S]
variable [Primcodable A] [Primcodable S]
 theorem primrec_words (a c : S) : Primrec (words a c) := by
  have h (z : S) : Primrec (fun x : ℕ × List (List S) => x.2.map (z::·)) :=
    Primrec.list_map Primrec.snd (Primrec.list_cons.comp (Primrec.const z) Primrec.snd).to₂
  exact (Primrec.nat_rec₁ [[]] (Primrec.list_append.comp (h a) (h c)).to₂).of_eq (by
    intro n; induction n <;> simp_all [words])

 theorem primrec_tail (a c : S) : Primrec (fun x : ℕ × List A × A => tail a c x.1 x.2.1 x.2.2) :=
  (Primrec.list_getD []).comp ((primrec_words a c).comp Primrec.fst)
    (Primrec.list_idxOf.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd))

 theorem primrec_encode (b a c : S) : Primrec (fun x : ℕ × List A × List A => encode b a c x.1 x.2.1 x.2.2) := by
  exact Primrec.list_flatMap (Primrec.snd.comp Primrec.snd)
    (Primrec.list_cons.comp (Primrec.const b) ((primrec_tail a c).comp
      ((Primrec.fst.comp Primrec.fst).pair ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)))).to₂

end FiniteAlgebraicEnvelopes.Bootstrap.LexBinary

namespace FiniteAlgebraicEnvelopes.Bootstrap.Rank
variable {P A B C : Type*} [DecidableEq A]

def word (ls : List A) (w : List A) : List ℕ := w.map ls.idxOf

noncomputable def less (ls : List A) (u v : List A) : Bool := by
  classical
  exact decide (List.Shortlex (fun a b : ℕ => a < b) (word ls u) (word ls v))

 theorem lex_map_iff {f : B → C} (hf : Function.Injective f) {r : C → C → Prop} (u v : List B) :
    List.Lex r (u.map f) (v.map f) ↔ List.Lex (fun a b => r (f a) (f b)) u v := by
  induction u generalizing v with
  | nil => cases v <;> simp
  | cons a u ih => cases v with
    | nil => simp
    | cons b v => simp only [List.map_cons,List.cons_lex_cons_iff,hf.eq_iff,ih]

 theorem shortlex_map_iff {f : B → C} (hf : Function.Injective f) {r : C → C → Prop} (u v : List B) :
    List.Shortlex r (u.map f) (v.map f) ↔ List.Shortlex (fun a b => r (f a) (f b)) u v := by
  simp only [List.shortlex_def,List.length_map,lex_map_iff hf]

 theorem index_injective (ls : List A) (i : B → A) (hi : Function.Injective i) (hm : ∀ b,i b∈ls) :
    Function.Injective (fun b => ls.idxOf (i b)) := by
  intro x y h
  exact hi ((List.idxOf_inj (hm x)).mp h)

 theorem less_map (ls : List A) (i : B → A) (hi : Function.Injective i) (hm : ∀ b,i b∈ls)
    (u v : List B) : less ls (u.map i) (v.map i)=true ↔
      List.Shortlex (fun a b => ls.idxOf (i a)<ls.idxOf (i b)) u v := by
  classical
  simp only [less,word,List.map_map,decide_eq_true_eq]
  exact shortlex_map_iff (index_injective ls i hi hm) u v

variable [Primcodable P] [Primcodable A]

 theorem primrec_word : Primrec₂ (word (A:=A)) :=
  Primrec.list_map Primrec.snd (Primrec.list_idxOf.comp Primrec.snd (Primrec.fst.comp Primrec.fst)).to₂

 theorem primrec_less (ls : P → List A) (hls : Primrec ls) :
    Primrec (fun x : P × List A × List A => less (ls x.1) x.2.1 x.2.2) := by
  classical
  exact (Search.primrec_shortlex Primrec.nat_lt).decide.comp
    (primrec_word.comp (hls.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    (primrec_word.comp (hls.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))

end FiniteAlgebraicEnvelopes.Bootstrap.Rank

namespace FiniteAlgebraicEnvelopes.MachineRealization.UniversalMachine
open Compiler.Simulator OneSided ParameterMachine
variable {S Γ Q : Type*} [DecidableEq Γ]

/-- Forget the parameter delimiter as an input/output letter. Work symbols and
    transitions are not changed. -/
def restrict (A : Alphabet (S ⊕ Unit) Γ) : Alphabet S Γ where
  blank := A.blank
  input s := A.input (.inl s)
  output g := (A.output g).bind fun a => match a with | .inl s => some s | .inr _ => none
  output_input s := by simp [A.output_input]
  output_blank := by simp [A.output_blank]

omit [DecidableEq Γ] in
 theorem restrict_decode (A : Alphabet (S ⊕ Unit) Γ)
    (hA : ∀ g a, A.output g=some a → g=A.input a) :
    ∀ g a, (restrict A).output g=some a → g=(restrict A).input a := by
  intro g a h
  obtain ⟨b,hb,hba⟩ := Option.bind_eq_some_iff.mp h
  cases b with
  | inr u => cases hba
  | inl s => cases hba; exact hA _ _ hb

omit [DecidableEq Γ] in
 theorem restrict_content (A : Alphabet (S ⊕ Unit) Γ) (w : List S) :
    content (restrict A) w=content A (w.map Sum.inl) := by
  simp only [content,List.map_map,Function.comp_def,restrict]
  rfl

omit [DecidableEq Γ] in
 theorem restrict_realizes (A : Alphabet (S ⊕ Unit) Γ) (M : Machine Q Γ)
    {f : List S → Part (List S)} {g : List (S ⊕ Unit) → Part (List (S ⊕ Unit))}
    (hM : Compiler.Word.Realizes A M g)
    (hg : ∀ w, g (w.map Sum.inl)=(f w).map (List.map Sum.inl)) :
    Compiler.Word.Realizes (restrict A) M f := by
  intro w out
  have hi : (List.map Sum.inl : List S → List (S ⊕ Unit)) out ∈ g (w.map Sum.inl) ↔ out ∈ f w := by
    rw [hg]
    constructor
    · intro h
      obtain ⟨y,hy,he⟩ := (Part.mem_map_iff _).mp h
      have hyout : y=out := List.map_injective_iff.mpr Sum.inl_injective he
      exact hyout ▸ hy
    · exact Part.mem_map _
  rw [←hi,hM,returns_iff A M,returns_iff (restrict A) M,restrict_content]
  simp only [List.map_map,Function.comp_def,restrict]

def letters (w : List (S ⊕ Unit)) : List S :=
  w.filterMap fun a => match a with | .inl s => some s | .inr _ => none

def parameter (w : List (S ⊕ Unit)) : ℕ :=
  (w.filterMap fun a => match a with | .inl _ => none | .inr _ => some ()).length - 1

 theorem letters_input (w : List S) (n : ℕ) :
    letters (w.map Sum.inl ++ List.replicate (n+1) (.inr ()))=w := by
  simp [letters,List.filterMap_map]

 theorem parameter_input (w : List S) (n : ℕ) :
    parameter (w.map Sum.inl ++ List.replicate (n+1) (.inr ()))=n := by
  simp [parameter,List.filterMap_map]

variable [Primcodable S]

 theorem primrec_letters : Primrec (letters (S := S)) := by
  have h : Primrec (fun a : S ⊕ Unit => match a with | .inl s => some s | .inr _ => none) :=
    (Primrec.sumCasesOn Primrec.id (Primrec.option_some.comp Primrec.snd).to₂ (Primrec.const none).to₂).of_eq
      (fun a => by cases a <;> rfl)
  exact Primrec.listFilterMap Primrec.id (h.comp Primrec.snd).to₂

 theorem primrec_parameter : Primrec (parameter (S := S)) := by
  have h : Primrec (fun a : S ⊕ Unit => match a with | .inl _ => none | .inr _ => some ()) :=
    (Primrec.sumCasesOn Primrec.id (Primrec.const none).to₂ (Primrec.const (some ())).to₂).of_eq
      (fun a => by cases a <;> rfl)
  exact Primrec.nat_sub.comp (Primrec.list_length.comp
    (Primrec.listFilterMap Primrec.id (h.comp Primrec.snd).to₂)) (Primrec.const 1)

def universal (f : ℕ → List S → Part (List S)) (w : List (S ⊕ Unit)) :
    Part (List (S ⊕ Unit)) := (f (parameter w) (letters w)).map (List.map Sum.inl)

omit [Primcodable S] in
 theorem universal_input (f : ℕ → List S → Part (List S)) (w : List S) (n : ℕ) :
    universal f (w.map Sum.inl ++ List.replicate (n+1) (.inr ()))=
      (f n w).map (List.map Sum.inl) := by
  rw [universal,parameter_input,letters_input]

 theorem partrec_universal {f : ℕ → List S → Part (List S)} (hf : Partrec₂ f) :
    Partrec (universal f) :=
  (hf.comp primrec_parameter.to_comp primrec_letters.to_comp).map
    ((Primrec.list_map Primrec.id (Primrec.sumInl.comp Primrec.snd).to₂).to_comp.comp Computable.snd).to₂

/-- The alphabet and all non-initializer control are now fixed once for the whole
    partial-recursive family. The only variable finite control is the explicit
    unary counter `Fin (n+2)`, not a choice of an evaluator for each index. -/
theorem exists_parameter_machine {S : Type} [Fintype S] [Primcodable S]
    {f : ℕ → List S → Part (List S)} (hf : Partrec₂ f) :
    ∃ (Γ Q : Type) (_ : Fintype Γ) (_ : Fintype Q) (_ : DecidableEq Γ)
      (A : Alphabet (S ⊕ Unit) Γ) (M : Machine Q Γ),
      (∀ g a, A.output g=some a → g=A.input a) ∧
      ∀ n, Compiler.Word.Realizes (restrict (alphabet A)) (machine A M (.inr ()) n) (f n) := by
  classical
  obtain ⟨Γ,Q,hΓ,hQ,A,M,hA,hM⟩ := WordEvaluator.exists_machine (partrec_universal hf)
  let : Fintype Γ := hΓ
  let : Fintype Q := hQ
  refine ⟨Γ,Q,hΓ,hQ,inferInstance,A,M,hA,?_⟩
  intro n
  exact restrict_realizes (alphabet A) (machine A M (.inr ()) n)
    (ParameterMachine.realizes A M (.inr ()) n hM) (fun w => universal_input f w n)

end FiniteAlgebraicEnvelopes.MachineRealization.UniversalMachine

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open Compiler Compiler.Simulator MachineRealization
open scoped Compiler.HeadCodec

abbrev Sigma := Fin 12

def markers : Selectors.Markers Sigma := ⟨11,7,8,9,10,by decide⟩

def raw (n : ℕ) (w : List Sigma) : Part (List Sigma) :=
  WordProgramming.eval ((Encodable.decode n : Option Nat.Partrec.Code).getD .zero) w

 theorem raw_encode (c : Nat.Partrec.Code) : raw (Encodable.encode c)=WordProgramming.eval c := by
  funext w
  simp [raw]

 theorem partrec_raw : Partrec₂ raw :=
  WordProgramming.partrec_eval.comp
    (Primrec.option_getD.comp (Primrec.decode.comp Primrec.fst) (Primrec.const .zero)).to_comp Computable.snd

variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable {Γ Q : Type*} [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q]
variable (A : Alphabet (Sigma ⊕ Unit) Γ) (M : Machine Q Γ)

local instance : DecidableEq (Tested.X Sigma Γ Q) := inferInstance

abbrev Y := Tested.Y Sigma Γ Q
abbrev Z (k : ℕ) := Fin k × Bool

noncomputable def yLetters (n : ℕ) : List (Y (Γ:=Γ) (Q:=Q)) := Tested.letters n
noncomputable def zLetters (k : ℕ) : List (Z k) := Static.letters (Z k)

/-- A single common width, chosen effectively only from finite alphabets. -/
noncomputable def width (k n : ℕ) : ℕ :=
  (yLetters (Γ:=Γ) (Q:=Q) n).length+(zLetters k).length+2

noncomputable def codeT (n : ℕ) : List (Y (Γ:=Γ) (Q:=Q)) → List Sigma :=
  LexBinary.encode 0 1 2 (width (Γ:=Γ) (Q:=Q) k n) (yLetters n)
noncomputable def codeG (n : ℕ) : List (Z k) → List Sigma :=
  LexBinary.encode 3 4 5 (width (Γ:=Γ) (Q:=Q) k n) (zLetters k)

noncomputable def testT (n : ℕ) : List (Y (Γ:=Γ) (Q:=Q)) → Part (Option (Tested.Class Sigma Γ Q)) :=
  Tested.family A M (.inr ()) (UniversalMachine.restrict (ParameterMachine.alphabet A))
    (fun p => raw p.1 p.2) n

noncomputable def testG (_ : ℕ) (w : List (Z k)) : Part (Option (List (Z k))) :=
  Part.some (some (WordProblem.testedClass s w))

noncomputable def tables (n : ℕ) : ℕ → Part (List (List Sigma × List Sigma)) :=
  Uniform.tables markers (yLetters n) (zLetters k) (codeT (k:=k) n) (codeG (Γ:=Γ) (Q:=Q) n)
    (Rank.less (yLetters n)) (Rank.less (zLetters k))
    (width (Γ:=Γ) (Q:=Q) k n+1) (width (Γ:=Γ) (Q:=Q) k n+1) (testT A M n) (testG s n)

omit [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] in
 theorem primrec_width : Primrec (width (Γ:=Γ) (Q:=Q) k) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp
    (Primrec.list_length.comp Tested.primrec_letters) (Primrec.const _)) (Primrec.const 2)

omit [Primcodable Γ] in
 theorem primrec_codeT : Primrec₂ (codeT (Γ:=Γ) (Q:=Q) (k:=k)) :=
  (LexBinary.primrec_encode 0 1 2).comp
    ((primrec_width.comp Primrec.fst).pair
      ((Tested.primrec_letters.comp Primrec.fst).pair Primrec.snd))

omit [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] in
 theorem primrec_codeG : Primrec₂ (codeG (Γ:=Γ) (Q:=Q) (k:=k)) :=
  (LexBinary.primrec_encode 3 4 5).comp
    ((primrec_width.comp Primrec.fst).pair ((Primrec.const _).pair Primrec.snd))

 theorem partrec_testT : Partrec₂ (testT A M) :=
  Tested.partrec_family A M (.inr ()) (UniversalMachine.restrict (ParameterMachine.alphabet A)) partrec_raw

 theorem partrec_tables (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => FiniteAlgebraicEnvelopes.evalWord s w=1)) :
    Partrec₂ (tables s A M) := by
  have hg : Partrec₂ (testG s) :=
    (Primrec.option_some.to_comp.comp ((WordProblem.computable_testedClass s h).comp Computable.snd)).partrec
  exact Uniform.partrec_tables markers yLetters (fun _ => zLetters k)
    codeT (codeG (Γ:=Γ) (Q:=Q)) (fun n => Rank.less (yLetters n)) (fun _ => Rank.less (zLetters k))
    (fun n => width (Γ:=Γ) (Q:=Q) k n+1) (fun n => width (Γ:=Γ) (Q:=Q) k n+1) (testT A M) (testG s)
    Tested.primrec_letters (Primrec.const _) primrec_codeT primrec_codeG
    (Rank.primrec_less _ Tested.primrec_letters) (Rank.primrec_less _ (Primrec.const _))
    (Primrec.nat_add.comp primrec_width (Primrec.const 1))
    (Primrec.nat_add.comp primrec_width (Primrec.const 1)) (partrec_testT A M) hg

/-- Literal source fixed point. No termination or contextual correctness is
    assumed: equality here also preserves divergence of the two procedures. -/
 theorem exists_fixed_point (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => FiniteAlgebraicEnvelopes.evalWord s w=1)) :
    ∃ n,raw n=tableNormal (tables s A M n) := by
  have hh := partrec_tableNormal_parameter (partrec_tables s A M h)
  have hc : Partrec₂ (fun c : Nat.Partrec.Code => tableNormal (tables s A M (Encodable.encode c))) :=
    hh.comp (Computable.encode.comp Computable.fst) Computable.snd
  obtain ⟨c,hc⟩ := WordProgramming.fixed_point hc
  exact ⟨Encodable.encode c,(raw_encode c).trans hc⟩

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes
namespace Effect
variable {A B C : Type*}
theorem traverse_map_output (f : A → Part B) (g : B → C) (ls : List A) :
    traverse (fun a => (f a).map g) ls = (traverse f ls).map (List.map g) := by
  induction ls with
  | nil => simp [traverse]
  | cons a ls ih =>
    simp only [traverse,ih,Part.bind_map,Part.map_bind,Part.map_map,Function.comp_def,List.map_cons]
end Effect

namespace Bootstrap.Uniform
variable {A B S Q : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq S] [DecidableEq Q]
variable (i : A → B) (hi : Function.Injective i)
variable (lt : List A → List A → Bool) (lt' : List B → List B → Bool)
variable (hlt : ∀ u v,lt' (u.map i) (v.map i)=lt u v)

def answerMap (v : List A × Option Q) : List B × Option Q := (v.1.map i,v.2)

include hlt

omit [DecidableEq A] [DecidableEq B] in
 theorem pickStep_map (q : Option Q) (w : List A) (v : List A × Option Q) :
    pickStep lt' q (w.map i) (answerMap i v)=(pickStep lt q w v).map i := by
  simp only [pickStep,answerMap,hlt]
  split <;> rfl

omit [DecidableEq A] [DecidableEq B] in
 theorem pick_map (ps : List (List A × Option Q)) (w : List A) (q : Option Q) :
    pick lt' (ps.map (answerMap i)) (w.map i) q=(pick lt ps w q).map i := by
  unfold pick
  induction ps generalizing w with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.foldl_cons,pickStep_map i lt lt' hlt,ih]

omit [DecidableEq A] [DecidableEq B] [DecidableEq S] in
 theorem output_map (code : List A → List S) (code' : List B → List S)
    (hc : ∀ w,code' (w.map i)=code w) (z : S) (ps : List (List A × Option Q)) (v : List A × Option Q) :
    output code' lt' z (ps.map (answerMap i)) (answerMap i v)=output code lt z ps v := by
  simp only [output,answerMap,pick_map i lt lt' hlt,hc]

omit [DecidableEq A] [DecidableEq B] in
 theorem table_map (code : List A → List S) (code' : List B → List S)
    (hc : ∀ w,code' (w.map i)=code w) (z : S) (ps : List (List A × Option Q)) :
    table code' lt' z (ps.map (answerMap i))=table code lt z ps := by
  simp only [table,List.flatMap_map]
  apply List.flatMap_congr
  intro v _
  rw [output_map i lt lt' hlt code code' hc z ps v]
  simp only [answerMap,hc,ne_eq,List.map_eq_nil_iff]

omit [DecidableEq A] [DecidableEq B] in
 theorem compute_map (code : List A → List S) (code' : List B → List S)
    (hc : ∀ w,code' (w.map i)=code w) (z : S) (ls : List A)
    (f : List A → Part (Option Q)) (g : List B → Part (Option Q))
    (hf : ∀ w,g (w.map i)=f w) (n : ℕ) :
    compute (ls.map i) code' lt' z g n=compute ls code lt z f n := by
  simp only [compute,words_map,←Effect.traverse_comp,hf]
  have hh : (fun w : List A => (f w).map (fun q => (w.map i,q))) =
      (fun w => ((f w).map (w,·)).map (answerMap i)) := by
    funext w
    simp only [Part.map_map,answerMap,Function.comp_def]
  rw [hh,Effect.traverse_map_output,Part.map_map]
  congr 1
  funext ps
  exact table_map i lt lt' hlt code code' hc z ps
end Bootstrap.Uniform
end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.Bootstrap.Uniform
variable {A S Q : Type*} [DecidableEq A] [DecidableEq S] [DecidableEq Q]
variable {r : A → A → Prop} [DecidableRel (List.Shortlex r)]

omit [DecidableEq A] in
 theorem pick_eq_canonical (ps : List (List A × Option Q)) (w : List A) (q : Option Q) :
    pick (fun u v => decide (List.Shortlex r u v)) ps w q=Canonical.pick (r:=r) ps w q := by
  have hh : pickStep (Q:=Q) (fun u v => decide (List.Shortlex r u v))=Canonical.pickStep (r:=r) := by
    funext q w v
    simp only [pickStep,Canonical.pickStep,decide_eq_true_eq]
  simp only [pick,Canonical.pick,hh]

variable [Fintype A] [Std.Trichotomous r] (wf : WellFounded r)
variable (C : BlockCode A S) (z : S) (q : List A → Option Q)
variable (ls : List A) (hls : ∀ a,a∈ls)
include hls

omit [DecidableEq A] [DecidableEq S] [Fintype A] in
 theorem output_full_support {n : ℕ} {w : List A} (hw : w.length≤n) :
    output C.encode (fun u v => decide (List.Shortlex r u v)) z
      ((words ls n).map fun v => (v,q v)) (w,q w)=Static.output C wf q z w := by
  have hps : ∀ p∈(words ls n).map (fun v => (v,q v)),p.2=q p.1 := by
    intro p hp
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hp
    rfl
  have hm : (Canonical.least wf q w,q w)∈(words ls n).map (fun v => (v,q v)) :=
    List.mem_map.mpr ⟨Canonical.least wf q w,(mem_words _ _ _).mpr
      ⟨(Canonical.least_length wf q w).trans hw,fun a _ => hls a⟩,
      by simp only [Canonical.least_class]⟩
  simp only [output,Static.output,pick_eq_canonical,Canonical.pick_eq_least wf q hps hm]

omit [DecidableEq A] in
 theorem table_full_support {n : ℕ} (p : List S × List S) :
    p∈table C.encode (fun u v => decide (List.Shortlex r u v)) z
      ((words ls n).map fun v => (v,q v)) ↔ p∈Static.table C wf q z n := by
  simp only [table,List.flatMap_map,List.mem_flatMap]
  constructor
  · rintro ⟨w,hw,h⟩
    have hlen := ((mem_words _ _ _).mp hw).1
    rw [output_full_support wf C z q ls hls hlen] at h
    split at h
    next hh =>
      obtain rfl := List.mem_singleton.mp h
      exact (Static.mem_table C wf q z).mpr ⟨w,hlen,hh.1,hh.2,rfl,rfl⟩
    next hh => simp at h
  · intro hp
    obtain ⟨w,hlen,hne,hout,ha,hb⟩ := (Static.mem_table C wf q z).mp hp
    refine ⟨w,(mem_words _ _ _).mpr ⟨hlen,fun a _ => hls a⟩,?_⟩
    rw [output_full_support wf C z q ls hls hlen,ite_eq_left ⟨hne,hout⟩]
    exact List.mem_singleton.mpr (Prod.ext ha hb)

omit [DecidableEq A] [Fintype A] [Std.Trichotomous r] hls in
 theorem compute_full_support {f : List A → Part (Option Q)} {n : ℕ}
    (hf : ∀ w,w.length≤n → q w∈f w) :
    table C.encode (fun u v => decide (List.Shortlex r u v)) z
      ((words ls n).map fun v => (v,q v))∈
        compute ls C.encode (fun u v => decide (List.Shortlex r u v)) z f n := by
  apply Part.mem_map
  apply Search.traverse_map
  intro w hw
  exact Part.mem_map _ (hf w ((mem_words _ _ _).mp hw).1)

omit [DecidableEq A] [Fintype A] [Std.Trichotomous r] in
 theorem compute_domain_support {f : List A → Part (Option Q)} {n : ℕ}
    (h : (compute ls C.encode (fun u v => decide (List.Shortlex r u v)) z f n).Dom) :
    ∀ w,w.length≤n → (f w).Dom := by
  obtain ⟨rs,hrs⟩ := Part.dom_iff_mem.mp h
  obtain ⟨ps,hps,_⟩ := (Part.mem_map_iff _).mp hrs
  intro w hw
  have hh := Effect.traverse_domain hps.1 w ((mem_words _ _ _).mpr ⟨hw,fun a _ => hls a⟩)
  obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp hh
  obtain ⟨a,ha,_⟩ := (Part.mem_map_iff _).mp hv
  exact ha.1

omit [DecidableEq A] in
 theorem compute_members_support {f : List A → Part (Option Q)} {n : ℕ}
    {rs : List (List S × List S)}
    (hrs : rs∈compute ls C.encode (fun u v => decide (List.Shortlex r u v)) z f n)
    (p : List S × List S) :
    p∈rs ↔ p∈Static.table C wf (Search.value f) z n := by
  have ht := compute_full_support (r:=r) C z (Search.value f) ls
    (fun w hw => Search.value_mem (compute_domain_support (r:=r) C z ls hls hrs.1 w hw))
  rw [Part.mem_unique hrs ht]
  exact table_full_support wf C z (Search.value f) ls hls p

end FiniteAlgebraicEnvelopes.Bootstrap.Uniform

namespace FiniteAlgebraicEnvelopes.Bootstrap
variable {S : Type*}
def RulesEq (rs rt : List (List S × List S)) : Prop := ∀ p,p∈rs ↔ p∈rt

 theorem step_rulesEq {rs rt : List (List S × List S)} (h : RulesEq rs rt) : Step rs=Step rt := by
  funext u v
  apply propext
  constructor <;> intro hs
  · cases hs with | apply hp x y => exact Step.apply ((h _).mp hp) x y
  · cases hs with | apply hp x y => exact Step.apply ((h _).mpr hp) x y

 theorem critical_rulesEq {rs rt : List (List S × List S)} (h : RulesEq rs rt) (n : ℕ) :
    Critical rs n ↔ Critical rt n := by
  simp only [Critical,Steps,step_rulesEq h,show ∀ p,p∈rs ↔ p∈rt from h]

namespace Selectors
variable [DecidableEq S] {a : Markers S}
 theorem allowed_rulesEq {rs rt : List (List S × List S)} (h : RulesEq rs rt) (s : Stage S) :
    allowed rs s=allowed rt s := by
  apply Bool.eq_iff_iff.mpr
  simp only [allowed_iff,step_rulesEq h]

 theorem choose_rulesEq {rs rt : List (List S × List S)} (h : RulesEq rs rt) (s : Stage S) (n : ℕ) :
    RulesEq (choose (a:=a) rs s n) (choose (a:=a) rt s n) := by
  intro p
  simp only [choose,allowed_rulesEq h s]
  split
  · simpa only [List.mem_append] using or_congr (h p) (Iff.rfl : p∈rules a s.size s.bodies ↔ p∈rules a s.size s.bodies)
  · exact h p

 theorem process_rulesEq {rs rt : List (List S × List S)} (h : RulesEq rs rt)
    (ss : ℕ → Stage S) (n j : ℕ) :
    RulesEq (process (a:=a) rs ss n j) (process (a:=a) rt ss n j) := by
  induction j with
  | zero => exact h
  | succ j ih => exact choose_rulesEq ih (ss j) n
end Selectors
end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes.Bootstrap.Uniform
variable {S A B Q R : Type*} [Primcodable S] [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq S] [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
variable {r : A → A → Prop} {s : B → B → Prop}
  [DecidableRel (List.Shortlex r)] [DecidableRel (List.Shortlex s)]
  [Std.Trichotomous r] [Std.Trichotomous s]
variable (a : Selectors.Markers S) (C : BlockCode A S) (D : BlockCode B S)
  (wf : WellFounded r) (wg : WellFounded s)
variable (ls : List A) (ms : List B) (hls : ∀ x,x∈ls) (hms : ∀ x,x∈ms)
variable (f : List A → Part (Option Q)) (g : List B → Part (Option R))

noncomputable def fullTables : ℕ → Part (List (List S × List S)) :=
  tables a ls ms C.encode D.encode (fun u v => decide (List.Shortlex r u v))
    (fun u v => decide (List.Shortlex s u v)) (C.width+1) (D.width+1) f g

include wf wg hls hms in
omit [DecidableEq A] [DecidableEq B] in
 theorem tables_members_support {n : ℕ} {rs : List (List S × List S)}
    (hrs : rs∈fullTables (r:=r) (s:=s) a C D ls ms f g n) :
    RulesEq rs (Selectors.process (a:=a)
      (Base.table C D wf wg (Search.value f) (Search.value g) a.zero n) (Selectors.stages a.zero) n n) := by
  obtain ⟨b,hb,rfl⟩ := (Part.mem_map_iff _).mp hrs
  obtain ⟨rc,hrc,h⟩ := Part.mem_bind_iff.mp hb
  obtain ⟨rd,hrd,rfl⟩ := (Part.mem_map_iff _).mp h
  apply Selectors.process_rulesEq
  intro p
  simp only [List.mem_append,Base.table,
    compute_members_support wf C a.zero ls hls hrc p,
    compute_members_support wg D a.zero ms hms hrd p]

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
  [Std.Trichotomous r] [Std.Trichotomous s] in
 theorem tables_domain_support {n : ℕ}
    (hf : ∀ w,w.length≤n/(C.width+1) → (f w).Dom)
    (hg : ∀ w,w.length≤n/(D.width+1) → (g w).Dom) :
    (fullTables (r:=r) (s:=s) a C D ls ms f g n).Dom := by
  have hc := compute_full_support (r:=r) C a.zero (Search.value f) ls
    (fun w hw => Search.value_mem (hf w hw))
  have hd := compute_full_support (r:=s) D a.zero (Search.value g) ms
    (fun w hw => Search.value_mem (hg w hw))
  apply Part.dom_iff_mem.mpr
  refine ⟨_,Part.mem_map _ (Part.mem_bind_iff.mpr ⟨_,hc,Part.mem_map _ hd⟩)⟩

include wf wg hls hms in
omit [DecidableEq A] [DecidableEq B] in
 theorem stable_support {k n : ℕ} (hkn : k≤n)
    {rk rn : List (List S × List S)}
    (hk : rk∈fullTables (r:=r) (s:=s) a C D ls ms f g k)
    (hn : rn∈fullTables (r:=r) (s:=s) a C D ls ms f g n) : Selectors.BoundedEq rk rn k := by
  have he := Selectors.tables_bounded (a:=a) (stages:=Selectors.stages a.zero)
    (fun _ _ hh => Base.bounded C D wf wg (Search.value f) (Search.value g) a.zero hh)
    (fun j w hw => Selectors.body_lt_size a.zero j hw) (Selectors.index_lt_size a.zero) hkn
  intro p hp
  exact (tables_members_support a C D wf wg ls ms hls hms f g hk p).trans
    ((he p hp).trans (tables_members_support a C D wf wg ls ms hls hms f g hn p).symm)

include wf wg hls hms in
omit [DecidableEq A] [DecidableEq B] in
 theorem good_support {t : S → S → Prop} (hcw : 1<C.width+1) (hdw : 1<D.width+1)
    (hc : ∀ a b,r a b → List.Lex t (C.block a) (C.block b))
    (hd : ∀ a b,s a b → List.Lex t (D.block a) (D.block b))
    (hC : ∀ b∈[a.zero,a.d,a.l,a.r,a.h],b∉C.Alphabet)
    (hD : ∀ b∈[a.zero,a.d,a.l,a.r,a.h],b∉D.Alphabet)
    (hCD : Disjoint C.Alphabet D.Alphabet) {n : ℕ}
    (hf : ∀ w,w.length≤n/(C.width+1) → (f w).Dom)
    (hg : ∀ w,w.length≤n/(D.width+1) → (g w).Dom)
    (hf0 : Search.value f []≠none) (hg0 : Search.value g []≠none)
    (hfc : Static.Contextual (Search.value f) (n/(C.width+1)))
    (hfi : Static.ZeroIdeal (Search.value f) (n/(C.width+1)))
    (hgc : Static.Contextual (Search.value g) (n/(D.width+1)))
    (hgi : Static.ZeroIdeal (Search.value g) (n/(D.width+1))) :
    GoodTable (r:=t) (fullTables (r:=r) (s:=s) a C D ls ms f g) n := by
  obtain ⟨rt,hrt,hdt,hct⟩ := Build.good a C D wf wg f g hcw hdw hc hd hC hD hCD hf hg hf0 hg0 hfc hfi hgc hgi
  obtain ⟨rs,hrs⟩ := Part.dom_iff_mem.mp (tables_domain_support (r:=r) (s:=s) a C D ls ms f g hf hg)
  have he : RulesEq rs rt := by
    rw [Build.tables_eq a C D wf wg hrt]
    exact tables_members_support a C D wf wg ls ms hls hms f g hrs
  exact ⟨rs,hrs,fun p hp => hdt p ((he p).mp hp),(critical_rulesEq he n).mpr hct⟩

end FiniteAlgebraicEnvelopes.Bootstrap.Uniform

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open Compiler Compiler.Simulator MachineRealization MachineRealization.ParameterCode
open scoped Compiler.HeadCodec
variable {Γ Q : Type*} [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q]

abbrev FiniteY (n : ℕ) := Word.Letter Sigma (Bool×Γ) (ParameterMachine.State Q n) ⊕ PartialAffine.Letter

def includeY (n : ℕ) : FiniteY (Γ:=Γ) (Q:=Q) n → Y (Γ:=Γ) (Q:=Q) :=
  Sum.map (Word.letterMap (encode n)) id

local instance : DecidableEq (Tested.X Sigma Γ Q) := inferInstance
local instance : DecidableEq (Y (Γ:=Γ) (Q:=Q)) := inferInstance
local instance (n : ℕ) : DecidableEq (Word.Letter Sigma (Bool×Γ) (ParameterMachine.State Q n)) := inferInstance
local instance (n : ℕ) : DecidableEq (FiniteY (Γ:=Γ) (Q:=Q) n) := inferInstance

omit [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
    [Primcodable Γ] [Primcodable Q] in
 theorem includeY_injective (n : ℕ) : Function.Injective (includeY (Γ:=Γ) (Q:=Q) n) := by
  exact Sum.map_injective.mpr ⟨Word.letterMap_injective (encode n) (encode_injective n),Function.injective_id⟩

omit [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q] in
 theorem includeY_mem (n : ℕ) (y : FiniteY (Γ:=Γ) (Q:=Q) n) : includeY n y∈yLetters n := by
  cases y with
  | inl y =>
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨_,(mem_letters_iff n _).mpr ⟨y,rfl⟩,rfl⟩
  | inr y =>
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨y,(by simp [Static.letters]),rfl⟩

omit [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q] in
 theorem mem_includeY_range (n : ℕ) {y : Y (Γ:=Γ) (Q:=Q)} (hy : y∈yLetters n) :
    ∃ v : FiniteY (Γ:=Γ) (Q:=Q) n,includeY n v=y := by
  rcases List.mem_append.mp hy with hy | hy
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hy
    obtain ⟨v,rfl⟩ := (mem_letters_iff n c).mp hc
    exact ⟨.inl v,rfl⟩
  · obtain ⟨v,_,rfl⟩ := List.mem_map.mp hy
    exact ⟨.inr v,rfl⟩

 theorem list_preimage {A B : Type*} (i : A → B) (ls : List B) (h : ∀ b∈ls,∃a,i a=b) :
    ∃ks : List A,ks.map i=ls := by
  induction ls with
  | nil => exact ⟨[],rfl⟩
  | cons b ls ih =>
    obtain ⟨a,rfl⟩ := h b (by simp)
    obtain ⟨ks,rfl⟩ := ih (fun x hx => h x (by simp [hx]))
    exact ⟨a::ks,rfl⟩

noncomputable def finiteLetters (n : ℕ) : List (FiniteY (Γ:=Γ) (Q:=Q) n) :=
  (list_preimage (includeY n) (yLetters n) (fun _ h => mem_includeY_range n h)).choose

omit [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q] in
 theorem map_finiteLetters (n : ℕ) : (finiteLetters (Γ:=Γ) (Q:=Q) n).map (includeY n)=yLetters n :=
  (list_preimage (includeY n) (yLetters n) (fun _ h => mem_includeY_range n h)).choose_spec

omit [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q] in
 theorem mem_finiteLetters (n : ℕ) (y : FiniteY (Γ:=Γ) (Q:=Q) n) : y∈finiteLetters n := by
  have h := includeY_mem n y
  rw [←map_finiteLetters n] at h
  obtain ⟨v,hv,he⟩ := List.mem_map.mp h
  exact (includeY_injective n he) ▸ hv

noncomputable def rankT (n : ℕ) (y : FiniteY (Γ:=Γ) (Q:=Q) n) : ℕ := @List.idxOf _ instBEqOfDecidableEq (includeY n y) (yLetters n)
noncomputable def rankG (k : ℕ) (z : Z k) : ℕ := @List.idxOf _ instBEqOfDecidableEq z (zLetters k)

omit [Primcodable Γ] [Primcodable Q] in
 theorem rankT_injective (n : ℕ) : Function.Injective (rankT (Γ:=Γ) (Q:=Q) n) := by
  exact Rank.index_injective _ _ (includeY_injective n) (includeY_mem n)
 theorem rankG_injective (k : ℕ) : Function.Injective (rankG k) := by
  exact Rank.index_injective _ id Function.injective_id (by intro x; simp [zLetters,Static.letters])

noncomputable def relT (n : ℕ) (u v : FiniteY (Γ:=Γ) (Q:=Q) n) : Prop := rankT n u<rankT n v
noncomputable def relG (k : ℕ) (u v : Z k) : Prop := rankG k u<rankG k v

omit [Primcodable Γ] [Primcodable Q] in
 theorem wf_relT (n : ℕ) : WellFounded (relT (Γ:=Γ) (Q:=Q) n) := InvImage.wf _ Nat.lt_wfRel.wf
 theorem wf_relG (k : ℕ) : WellFounded (relG k) := InvImage.wf _ Nat.lt_wfRel.wf

instance tri_relT (n : ℕ) : Std.Trichotomous (relT (Γ:=Γ) (Q:=Q) n) := ⟨fun a b hab hba =>
  rankT_injective n (by change ¬rankT n a < rankT n b at hab; change ¬rankT n b < rankT n a at hba; omega)⟩
instance tri_relG (k : ℕ) : Std.Trichotomous (relG k) := ⟨fun a b hab hba =>
  rankG_injective k (by change ¬rankG k a < rankG k b at hab; change ¬rankG k b < rankG k a at hba; omega)⟩
noncomputable instance dec_relT (n : ℕ) : DecidableRel (relT (Γ:=Γ) (Q:=Q) n) := fun _ _ => Nat.decLt _ _
noncomputable instance dec_relG (k : ℕ) : DecidableRel (relG k) := fun _ _ => Nat.decLt _ _

noncomputable instance dec_shortlexT (n : ℕ) : DecidableRel (List.Shortlex (relT (Γ:=Γ) (Q:=Q) n)) := Classical.decRel _
noncomputable instance dec_shortlexG (k : ℕ) : DecidableRel (List.Shortlex (relG k)) := Classical.decRel _

omit [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q] in
 theorem widthBoundT (k n : ℕ) : (yLetters (Γ:=Γ) (Q:=Q) n).length≤2^(width (Γ:=Γ) (Q:=Q) k n) := by
  have h : width (Γ:=Γ) (Q:=Q) k n < 2^(width (Γ:=Γ) (Q:=Q) k n) := Nat.lt_two_pow_self
  unfold width at *
  omega
omit [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q] in
 theorem widthBoundG (k n : ℕ) : (zLetters k).length≤2^(width (Γ:=Γ) (Q:=Q) k n) := by
  have h : width (Γ:=Γ) (Q:=Q) k n < 2^(width (Γ:=Γ) (Q:=Q) k n) := Nat.lt_two_pow_self
  unfold width at *
  omega

noncomputable def finiteCodeT (k n : ℕ) : BlockCode (FiniteY (Γ:=Γ) (Q:=Q) n) Sigma :=
  LexBinary.code 0 1 2 (by decide) (by decide) (by decide) (width k n) (yLetters n)
    (widthBoundT k n) (includeY n) (includeY_injective n) (includeY_mem n)
noncomputable def finiteCodeG (k n : ℕ) : BlockCode (Z k) Sigma :=
  LexBinary.code 3 4 5 (by decide) (by decide) (by decide) (width (Γ:=Γ) (Q:=Q) k n) (zLetters k)
    (widthBoundG k n) id Function.injective_id (by intro x; simp [zLetters,Static.letters])

omit [Primcodable Γ] [Primcodable Q] in
 theorem finiteCodeT_encode (k n : ℕ) (w : List (FiniteY (Γ:=Γ) (Q:=Q) n)) :
    (finiteCodeT k n).encode w=codeT (k:=k) n (w.map (includeY n)) :=
  LexBinary.code_encode ..
omit [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q] in
 theorem finiteCodeG_encode (k n : ℕ) (w : List (Z k)) :
    (finiteCodeG (Γ:=Γ) (Q:=Q) k n).encode w=codeG (Γ:=Γ) (Q:=Q) n w := by
  simpa [finiteCodeG,codeG] using LexBinary.code_encode 3 4 5 (by decide) (by decide) (by decide)
    (width (Γ:=Γ) (Q:=Q) k n) (zLetters k) (widthBoundG k n) id Function.injective_id (by intro x; simp [zLetters,Static.letters]) w

omit [Primcodable Γ] [Primcodable Q] in
 theorem lessT_map (n : ℕ) (u v : List (FiniteY (Γ:=Γ) (Q:=Q) n)) :
    Rank.less (yLetters n) (u.map (includeY n)) (v.map (includeY n))=decide (List.Shortlex (relT n) u v) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  change _ ↔ List.Shortlex (fun a b => @List.idxOf _ instBEqOfDecidableEq (includeY n a) (yLetters n)<@List.idxOf _ instBEqOfDecidableEq (includeY n b) (yLetters n)) u v
  exact Rank.less_map (yLetters n) (includeY n) (includeY_injective n) (includeY_mem n) u v
 theorem lessG_eq (k : ℕ) (u v : List (Z k)) :
    Rank.less (zLetters k) u v=decide (List.Shortlex (relG k) u v) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  change _ ↔ List.Shortlex (fun a b => @List.idxOf _ instBEqOfDecidableEq a (zLetters k)<@List.idxOf _ instBEqOfDecidableEq b (zLetters k)) u v
  simpa using Rank.less_map (zLetters k) id Function.injective_id (by intro x; simp [zLetters,Static.letters]) u v

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.Bootstrap
namespace LexBinary
variable {A B S : Type*} [DecidableEq A] [DecidableEq S]
omit [DecidableEq S] in
 theorem alphabet_bound (b a c : S) (hba : b≠a) (hbc : b≠c) (hac : a≠c)
    (d : ℕ) (ls : List A) (hls : ls.length≤2^d)
    (i : B → A) (hi : Function.Injective i) (hm : ∀ x,i x∈ls) {s : S}
    (hs : s∈(code b a c hba hbc hac d ls hls i hi hm).Alphabet) : s=b ∨ s=a ∨ s=c := by
  obtain ⟨x,hx⟩ := hs
  rcases List.mem_cons.mp hx with rfl | hx
  · exact Or.inl rfl
  · right
    change s∈tail a c d ls (i x) at hx
    rw [tail,List.getD_eq_getElem _ _ (index_bound d ls hls (hm x))] at hx
    exact mem_letters (List.getElem_mem _) hx
end LexBinary

namespace Source
open Compiler Compiler.Simulator MachineRealization MachineRealization.ParameterCode
open scoped Compiler.HeadCodec
variable {Γ Q : Type*} [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q]
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable (A : Alphabet (Sigma ⊕ Unit) Γ) (M : Machine Q Γ)

local instance : DecidableEq (Tested.X Sigma Γ Q) := inferInstance
local instance : DecidableEq (Y (Γ:=Γ) (Q:=Q)) := inferInstance
local instance (n : ℕ) : DecidableEq (Word.Letter Sigma (Bool×Γ) (ParameterMachine.State Q n)) := inferInstance
local instance (n : ℕ) : DecidableEq (FiniteY (Γ:=Γ) (Q:=Q) n) := inferInstance
local instance (n : ℕ) : Fintype (Word.Letter Sigma (Bool×Γ) (ParameterMachine.State Q n)) := inferInstance

noncomputable def finiteTest (n : ℕ) (w : List (FiniteY (Γ:=Γ) (Q:=Q) n)) := testT A M n (w.map (includeY n))

noncomputable def finiteTables (n : ℕ) :=
  Uniform.fullTables (r:=relT n) (s:=relG k) markers (finiteCodeT (Γ:=Γ) (Q:=Q) k n) (finiteCodeG (Γ:=Γ) (Q:=Q) k n)
    (finiteLetters n) (zLetters k) (finiteTest A M n) (testG s n)

omit [Primcodable Γ] in
 theorem tables_eq_finite (n : ℕ) : tables s A M n=finiteTables s A M n := by
  have hT (j : ℕ) : Uniform.compute (yLetters n) (codeT (k:=k) n) (Rank.less (yLetters n)) markers.zero (testT A M n) j=
      Uniform.compute (finiteLetters n) (finiteCodeT (Γ:=Γ) (Q:=Q) k n).encode (fun u v => decide (List.Shortlex (relT n) u v))
        markers.zero (finiteTest A M n) j := by
    simpa only [map_finiteLetters] using Uniform.compute_map (includeY n) _ _ (lessT_map n) _ _ (fun w => (finiteCodeT_encode k n w).symm)
      markers.zero (finiteLetters n) (finiteTest A M n) (testT A M n) (fun _ => rfl) j
  have hG : codeG (Γ:=Γ) (Q:=Q) (k:=k) n=(finiteCodeG (Γ:=Γ) (Q:=Q) k n).encode :=
    funext (fun w => (finiteCodeG_encode k n w).symm)
  have hlG : Rank.less (zLetters k)=(fun u v => decide (List.Shortlex (relG k) u v)) :=
    funext (fun u => funext (lessG_eq k u))
  funext j
  simp only [tables,finiteTables,Uniform.fullTables,Uniform.tables,Uniform.bases,hT,hG,hlG]
  rfl

omit [Primcodable Γ] in
 theorem stable (n : ℕ) {a b : ℕ} (hab : a≤b) {ra rb : List (List Sigma × List Sigma)}
    (ha : ra∈tables s A M n a) (hb : rb∈tables s A M n b) : Selectors.BoundedEq ra rb a := by
  rw [tables_eq_finite] at ha hb
  exact Uniform.stable_support markers (finiteCodeT (Γ:=Γ) (Q:=Q) k n) (finiteCodeG (Γ:=Γ) (Q:=Q) k n) (wf_relT n) (wf_relG k)
    (finiteLetters n) (zLetters k) (mem_finiteLetters n) (by intro x; simp [zLetters,Static.letters])
    (finiteTest A M n) (testG s n) hab ha hb

omit [Primcodable Γ] [Primcodable Q] in
 theorem codeT_order (k n : ℕ) (a b : FiniteY (Γ:=Γ) (Q:=Q) n) (hab : relT n a b) :
    List.Lex (fun u v : Sigma => u<v) ((finiteCodeT (Γ:=Γ) (Q:=Q) k n).block a) ((finiteCodeT (Γ:=Γ) (Q:=Q) k n).block b) :=
  LexBinary.code_order 0 1 2 (by decide) (by decide) (by decide) (by decide) _ _ _ _ _ _ hab
omit [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q] in
 theorem codeG_order (k n : ℕ) (a b : Z k) (hab : relG k a b) :
    List.Lex (fun u v : Sigma => u<v) ((finiteCodeG (Γ:=Γ) (Q:=Q) k n).block a) ((finiteCodeG (Γ:=Γ) (Q:=Q) k n).block b) :=
  LexBinary.code_order 3 4 5 (by decide) (by decide) (by decide) (by decide) _ _ _ _ _ _ hab

omit [Primcodable Γ] [Primcodable Q] in
 theorem codeT_alphabet (k n : ℕ) {u : Sigma} (hu : u∈(finiteCodeT (Γ:=Γ) (Q:=Q) k n).Alphabet) :
    u=0 ∨ u=1 ∨ u=2 := by
  exact LexBinary.alphabet_bound _ _ _ _ _ _ _ _ _ _ _ _ hu
omit [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q] in
 theorem codeG_alphabet (k n : ℕ) {u : Sigma} (hu : u∈(finiteCodeG (Γ:=Γ) (Q:=Q) k n).Alphabet) :
    u=3 ∨ u=4 ∨ u=5 := by
  exact LexBinary.alphabet_bound _ _ _ _ _ _ _ _ _ _ _ _ hu

omit [Primcodable Γ] [Primcodable Q] in
 theorem codeT_avoid (k n : ℕ) : ∀ b∈[markers.zero,markers.d,markers.l,markers.r,markers.h],
    b∉(finiteCodeT (Γ:=Γ) (Q:=Q) k n).Alphabet := by
  intro b hb hc
  have h := codeT_alphabet k n hc
  simp [markers] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl <;> norm_num [Fin.ext_iff] at h
omit [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q] in
 theorem codeG_avoid (k n : ℕ) : ∀ b∈[markers.zero,markers.d,markers.l,markers.r,markers.h],
    b∉(finiteCodeG (Γ:=Γ) (Q:=Q) k n).Alphabet := by
  intro b hb hc
  have h := codeG_alphabet k n hc
  simp [markers] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl <;> norm_num [Fin.ext_iff] at h
omit [Primcodable Γ] [Primcodable Q] in
 theorem codes_disjoint (k n : ℕ) : Disjoint (finiteCodeT (Γ:=Γ) (Q:=Q) k n).Alphabet (finiteCodeG (Γ:=Γ) (Q:=Q) k n).Alphabet := by
  apply Set.disjoint_left.mpr
  intro b hb hc
  have h := codeT_alphabet k n hb
  have j := codeG_alphabet k n hc
  rcases h with rfl|rfl|rfl <;> norm_num [Fin.ext_iff] at j

omit [Primcodable Γ] in
 theorem good_of_tests (n j : ℕ)
    (hf : ∀ w : List (FiniteY (Γ:=Γ) (Q:=Q) n),w.length≤j/(width (Γ:=Γ) (Q:=Q) k n+1) → (finiteTest A M n w).Dom)
    (hf0 : Search.value (finiteTest A M n) []≠none)
    (hfc : Static.Contextual (Search.value (finiteTest A M n)) (j/(width (Γ:=Γ) (Q:=Q) k n+1)))
    (hfi : Static.ZeroIdeal (Search.value (finiteTest A M n)) (j/(width (Γ:=Γ) (Q:=Q) k n+1)))
    (hg0 : Search.value (testG s n) []≠none)
    (hgc : Static.Contextual (Search.value (testG s n)) (j/(width (Γ:=Γ) (Q:=Q) k n+1)))
    (hgi : Static.ZeroIdeal (Search.value (testG s n)) (j/(width (Γ:=Γ) (Q:=Q) k n+1))) :
    GoodTable (r:=fun u v : Sigma => u<v) (tables s A M n) j := by
  rw [tables_eq_finite]
  apply Uniform.good_support markers (finiteCodeT (Γ:=Γ) (Q:=Q) k n) (finiteCodeG (Γ:=Γ) (Q:=Q) k n) (wf_relT n) (wf_relG k)
    (finiteLetters n) (zLetters k) (mem_finiteLetters n) (by intro x; simp [zLetters,Static.letters])
    (finiteTest A M n) (testG s n)
  · change 1<width (Γ:=Γ) (Q:=Q) k n+1
    unfold width
    omega
  · change 1<width (Γ:=Γ) (Q:=Q) k n+1
    unfold width
    omega
  · exact codeT_order k n
  · exact codeG_order k n
  · exact codeT_avoid k n
  · exact codeG_avoid k n
  · exact codes_disjoint k n
  · exact hf
  · intro w hw; trivial
  · exact hf0
  · exact hg0
  · exact hfc
  · exact hfi
  · exact hgc
  · exact hgi

end Source
end FiniteAlgebraicEnvelopes.Bootstrap

end OAI
