import OAI.Computability.FiniteCompiler.UniformMachines

namespace OAI

/-!
Uniform validation, simulation, and finite control.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {P H B T : Type*} [Primcodable P] [Primcodable H] [Primcodable B] [Primcodable T]
variable (table : P → Table H B T)
variable (hb : Primrec (fun x : P × H => (table x.1).boundary x.2))
variable (hc : Primrec (fun x : P × H × B × T => (table x.1).cell x.2.1 x.2.2.1 x.2.2.2))
variable (hd : Primrec (fun x : P × H => decide ((table x.1).direction x.2 = .right)))

include hb hc in
theorem primrec_rightStep : Primrec (fun x : P × Sector H B T => rightStep (table x.1) x.2) := by
  let X := P × Sector H B T
  have hv : Primrec (fun x : X => x.2) := Primrec.snd
  have hl := Sector.primrec_left.comp hv
  have hh := Sector.primrec_head.comp hv
  have hr := Sector.primrec_right.comp hv
  have hla := Sector.primrec_lb.comp hv
  have hra := Sector.primrec_rb.comp hv
  have hnil : Primrec (fun x : X => if x.2.rightBoundary then
      ((table x.1).boundary x.2.head).map (fun q => {x.2 with head := q}) else none) := by
    simp only [← Bool.cond_eq_ite]
    apply Primrec.cond hra
    · apply Primrec.option_map (hb.comp (Primrec.fst.pair hh))
      exact (Sector.primrec_mk (hl.comp Primrec.fst) Primrec.snd (hr.comp Primrec.fst)
        (hla.comp Primrec.fst) (hra.comp Primrec.fst)).to₂
    · exact Primrec.const none
  have hcons : Primrec₂ (fun (x : X) (p : (B×T) × List (B×T)) =>
      ((table x.1).cell x.2.head p.1.1 p.1.2).map fun a =>
        if a.cross then {x.2 with left := (p.1.1,a.tag)::x.2.left,head := a.head,right := p.2}
        else {x.2 with head := a.head,right := (p.1.1,a.tag)::p.2}) := by
    unfold Primrec₂
    apply Primrec.option_map (hc.comp
      ((Primrec.fst.comp Primrec.fst).pair ((hh.comp Primrec.fst).pair
        ((Primrec.fst.comp (Primrec.fst.comp Primrec.snd)).pair
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))))
    unfold Primrec₂
    let Y := (X × ((B×T) × List (B×T))) × Instruction H T
    have hx : Primrec (fun y : Y => y.1.1) := Primrec.fst.comp Primrec.fst
    have hp : Primrec (fun y : Y => y.1.2) := Primrec.snd.comp Primrec.fst
    have hi : Primrec (fun y : Y => y.2) := Primrec.snd
    have hcell : Primrec (fun y : Y => (y.1.2.1.1,y.2.tag)) :=
      (Primrec.fst.comp (Primrec.fst.comp hp)).pair (Instruction.primrec_tag.comp hi)
    simp only [← Bool.cond_eq_ite]
    apply Primrec.cond (Instruction.primrec_cross.comp hi)
    · exact Sector.primrec_mk (Primrec.list_cons.comp hcell (hl.comp hx))
        (Instruction.primrec_head.comp hi) (Primrec.snd.comp hp) (hla.comp hx) (hra.comp hx)
    · exact Sector.primrec_mk (hl.comp hx) (Instruction.primrec_head.comp hi)
        (Primrec.list_cons.comp hcell (Primrec.snd.comp hp)) (hla.comp hx) (hra.comp hx)
  exact (Primrec.list_casesOn hr hnil hcons).of_eq fun x => by
    cases h : x.2.right with
    | nil => simp [rightStep,h]
    | cons a l => cases a; simp [rightStep,h]

include hb hc hd in
theorem primrec_step : Primrec (fun x : P × Sector H B T => step (table x.1) x.2) := by
  have hr := primrec_rightStep table hb hc
  exact (Primrec.cond (hd.comp (Primrec.fst.pair (Sector.primrec_head.comp Primrec.snd)))
    hr (Primrec.option_map (hr.comp (Primrec.fst.pair (Scan.primrec_flip.comp Primrec.snd)))
      (Scan.primrec_flip.comp Primrec.snd).to₂)).of_eq fun x => by
        simpa only [Bool.cond_decide] using (step_rightStep (table x.1) x.2).symm

/-- Only control heads in the supplied literal support are enumerated. The
    ambient coded head type need not be finite. -/
noncomputable def sectorList [Fintype B] [Fintype T] (heads : List H) (n : ℕ) : List (Sector H B T) :=
  heads.flatMap fun q => (wordList (B×T) n).flatMap fun l =>
    (wordList (B×T) n).flatMap fun r =>
      [⟨l,q,r,false,false⟩,⟨l,q,r,false,true⟩,⟨l,q,r,true,false⟩,⟨l,q,r,true,true⟩]

omit [Primcodable H] [Primcodable B] [Primcodable T] in
@[simp] theorem mem_sectorList [Fintype B] [Fintype T] (heads : List H) (n : ℕ) (v : Sector H B T) :
    v ∈ sectorList heads n ↔ v.head ∈ heads ∧ v.left.length ≤ n ∧ v.right.length ≤ n := by
  rcases v with ⟨l,q,r,a,b⟩
  cases a <;> cases b <;> simp [sectorList,Sector.mk.injEq]

variable [Fintype B] [Fintype T]
theorem primrec_sectorList : Primrec (fun x : List H × ℕ => sectorList (B := B) (T := T) x.1 x.2) := by
  apply Primrec.list_flatMap Primrec.fst
  unfold Primrec₂
  apply Primrec.list_flatMap (primrec_wordList.comp (Primrec.snd.comp Primrec.fst))
  unfold Primrec₂
  apply Primrec.list_flatMap (primrec_wordList.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  unfold Primrec₂
  have hm (a b : Bool) : Primrec (fun p : (((List H × ℕ) × H) × List (B×T)) × List (B×T) =>
      (⟨p.1.2,p.1.1.2,p.2,a,b⟩ : Sector H B T)) :=
    Sector.primrec_mk (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
      (Primrec.const a) (Primrec.const b)
  exact Primrec.list_cons.comp (hm false false) (Primrec.list_cons.comp (hm false true)
    (Primrec.list_cons.comp (hm true false) (Primrec.list_cons.comp (hm true true) (Primrec.const []))))

variable [DecidableEq H] [DecidableEq B] [DecidableEq T]
noncomputable def universeList (heads : List H) (v : Sector H B T) : List (Sector H B T) :=
  (sectorList heads (v.left.length+v.right.length)).filter fun w => baseSkeleton w=baseSkeleton v

omit [DecidableEq H] [DecidableEq T] in
omit [Primcodable H] [Primcodable B] [Primcodable T] in
@[simp] theorem mem_universeList (heads : List H) (v w : Sector H B T) :
    w ∈ universeList heads v ↔ w.head ∈ heads ∧ baseSkeleton w=baseSkeleton v := by
  simp only [universeList,List.mem_filter,mem_sectorList,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h,_,_⟩,he⟩; exact ⟨h,he⟩
  · rintro ⟨h,he⟩
    have hl := skeleton_length he
    exact ⟨⟨h,by omega,by omega⟩,he⟩

omit [DecidableEq H] [DecidableEq T] in
theorem primrec_universeList :
    Primrec (fun x : List H × Sector H B T => universeList x.1 x.2) := by
  apply primrec_listFilter (primrec_sectorList.comp (Primrec.fst.pair
    (Primrec.nat_add.comp (Primrec.list_length.comp (Sector.primrec_left.comp Primrec.snd))
      (Primrec.list_length.comp (Sector.primrec_right.comp Primrec.snd)))))
  exact (Primrec.eq.decide.comp (primrec_baseSkeleton.comp Primrec.snd)
    (primrec_baseSkeleton.comp (Primrec.snd.comp Primrec.fst))).to₂

noncomputable def componentList (support : P → List H) (x : P × Sector H B T) : List (Sector H B T) :=
  FiniteAlgebraicEnvelopes.Effect.Graph.component (fun a b => decide (step (table x.1) a=some b)) (universeList (support x.1) x.2) x.2

include hb hc hd in
theorem primrec_componentList {support : P → List H} (hs : Primrec support) :
    Primrec (componentList table support) := by
  have he : Primrec (fun x : P × Sector H B T × Sector H B T =>
      decide (step (table x.1) x.2.1=some x.2.2)) :=
    Primrec.eq.decide.comp ((primrec_step table hb hc hd).comp
      (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
      (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd))
  exact (primrec_component_family (r := fun p a b => decide (step (table p) a=some b)) he).comp (Primrec.fst.pair
    ((primrec_universeList.comp ((hs.comp Primrec.fst).pair Primrec.snd)).pair Primrec.snd))

end FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform

namespace FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open Simulator

inductive Static (S : Type*)
  | start | rewind : Resume S → Static S | scan : Resume S → Static S
  | finish | ok
  deriving DecidableEq, Fintype

variable {S Q Q' H C : Type*}

def ofStatic : Static S → Simulator.Head S Q
  | .start => .start
  | .rewind r => .rewind r
  | .scan r => .scan r
  | .finish => .finish
  | .ok => .ok

def dynamic (p : Bool × Q) : Simulator.Head S Q := if p.1 then .left p.2 else .run p.2

def simCode : Simulator.Head S Q ≃ Static S ⊕ (Bool × Q) where
  toFun
    | .start => .inl .start
    | .rewind r => .inl (.rewind r)
    | .scan r => .inl (.scan r)
    | .finish => .inl .finish
    | .ok => .inl .ok
    | .run q => .inr (false,q)
    | .left q => .inr (true,q)
  invFun := Sum.elim ofStatic dynamic
  left_inv q := by cases q <;> rfl
  right_inv q := by
    cases q with
    | inl q => cases q <;> rfl
    | inr q => rcases q with ⟨a,q⟩; cases a <;> rfl

def controlCode : Control.Head S Q ≃ Fin 5 ⊕ Simulator.Head S Q where
  toFun
    | .initial => .inl 0
    | .left => .inl 1
    | .right => .inl 2
    | .workspace => .inl 3
    | .suffix => .inl 4
    | .machine q => .inr q
  invFun
    | .inl k => if k=0 then .initial else if k=1 then .left else if k=2 then .right
      else if k=3 then .workspace else .suffix
    | .inr q => .machine q
  left_inv q := by cases q <;> rfl
  right_inv q := by
    cases q with
    | inl k => fin_cases k <;> rfl
    | inr q => rfl

def surfaceCode : Surface.Head H ≃ Fin 3 ⊕ H where
  toFun | .raw => .inl 0 | .pending => .inl 1 | .cleanup => .inl 2 | .internal q => .inr q
  invFun | .inl k => if k=0 then .raw else if k=1 then .pending else .cleanup
         | .inr q => .internal q
  left_inv q := by cases q <;> rfl
  right_inv q := by cases q with
    | inl k => fin_cases k <;> rfl
    | inr q => rfl

def pathCode : Path.Letter C H ≃ Fin 3 ⊕ (C ⊕ (C ⊕ H)) where
  toFun | .zero => .inl 0 | .enter => .inl 1 | .leave => .inl 2
        | .left c => .inr (.inl c) | .right c => .inr (.inr (.inl c))
        | .head q => .inr (.inr (.inr q))
  invFun | .inl k => if k=0 then .zero else if k=1 then .enter else .leave
         | .inr (.inl c) => .left c | .inr (.inr (.inl c)) => .right c
         | .inr (.inr (.inr q)) => .head q
  left_inv q := by cases q <;> rfl
  right_inv q := by
    cases q with
    | inl k => fin_cases k <;> rfl
    | inr q => cases q with
      | inl c => rfl
      | inr q => cases q <;> rfl

noncomputable scoped instance staticPrimcodable [Fintype S] : Primcodable (Static S) :=
  Effect.finitePrimcodable _
noncomputable scoped instance simulatorPrimcodable [Fintype S] [Primcodable Q] :
    Primcodable (Simulator.Head S Q) := Primcodable.ofEquiv _ simCode
noncomputable scoped instance controlPrimcodable [Fintype S] [Primcodable Q] :
    Primcodable (Control.Head S Q) := Primcodable.ofEquiv _ controlCode
scoped instance surfacePrimcodable [Primcodable H] : Primcodable (Surface.Head H) :=
  Primcodable.ofEquiv _ surfaceCode
scoped instance pathPrimcodable [Primcodable C] [Primcodable H] : Primcodable (Path.Letter C H) :=
  Primcodable.ofEquiv _ pathCode

variable [Fintype S] [Primcodable Q]
theorem primrec_simCode : Primrec (simCode (S := S) (Q := Q)) := Primrec.of_equiv
theorem primrec_simDecode : Primrec (simCode (S := S) (Q := Q)).symm := Primrec.of_equiv_symm
theorem primrec_ofStatic : Primrec (ofStatic (S := S) (Q := Q)) :=
  primrec_simDecode.comp Primrec.sumInl
theorem primrec_dynamic : Primrec (dynamic (S := S) (Q := Q)) :=
  primrec_simDecode.comp Primrec.sumInr

theorem primrec_controlCode : Primrec (controlCode (S := S) (Q := Q)) := Primrec.of_equiv
theorem primrec_controlDecode : Primrec (controlCode (S := S) (Q := Q)).symm := Primrec.of_equiv_symm
theorem primrec_machine : Primrec (Control.Head.machine (S := S) (Q := Q)) :=
  primrec_controlDecode.comp Primrec.sumInr

theorem primrec_surfaceCode [Primcodable H] : Primrec (surfaceCode (H := H)) := Primrec.of_equiv
theorem primrec_surfaceDecode [Primcodable H] : Primrec (surfaceCode (H := H)).symm := Primrec.of_equiv_symm
theorem primrec_internal [Primcodable H] : Primrec (Surface.Head.internal (H := H)) :=
  primrec_surfaceDecode.comp Primrec.sumInr

theorem primrec_pathCode [Primcodable C] [Primcodable H] : Primrec (pathCode (C := C) (H := H)) :=
  Primrec.of_equiv
theorem primrec_pathDecode [Primcodable C] [Primcodable H] : Primrec (pathCode (C := C) (H := H)).symm :=
  Primrec.of_equiv_symm

end FiniteAlgebraicEnvelopes.Compiler.HeadCodec

namespace FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open Simulator
open scoped HeadCodec
variable {S Γ Q Q' P : Type*}

def stateMap (f : Q → Q') : Simulator.Head S Q → Simulator.Head S Q'
  | .start => .start | .rewind r => .rewind r | .scan r => .scan r
  | .run q => .run (f q) | .left q => .left (f q) | .finish => .finish | .ok => .ok

def controlMap (f : Q → Q') : Control.Head S Q → Control.Head S Q'
  | .initial => .initial | .left => .left | .right => .right
  | .workspace => .workspace | .suffix => .suffix | .machine q => .machine (stateMap f q)

def commandMap (f : Q → Q') (c : Command Q Γ) : Command Q' Γ := ⟨f c.state,c.write,c.move⟩

def commandCode : Command Q Γ ≃ Q × Γ × Move where
  toFun c := (c.state,c.write,c.move)
  invFun c := ⟨c.1,c.2.1,c.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable scoped instance movePrimcodable : Primcodable Move := Effect.finitePrimcodable _
noncomputable scoped instance commandPrimcodable [Primcodable Q] [Primcodable Γ] : Primcodable (Command Q Γ) :=
  Primcodable.ofEquiv _ commandCode

theorem primrec_commandCode [Primcodable Q] [Primcodable Γ] : Primrec (commandCode (Q := Q) (Γ := Γ)) :=
  Primrec.of_equiv

theorem primrec_commandState [Primcodable Q] [Primcodable Γ] : Primrec (Command.state (Q := Q) (Γ := Γ)) :=
  Primrec.fst.comp primrec_commandCode

theorem primrec_commandWrite [Primcodable Q] [Primcodable Γ] : Primrec (Command.write (Q := Q) (Γ := Γ)) :=
  Primrec.fst.comp (Primrec.snd.comp primrec_commandCode)

theorem primrec_commandMove [Primcodable Q] [Primcodable Γ] : Primrec (Command.move (Q := Q) (Γ := Γ)) :=
  Primrec.snd.comp (Primrec.snd.comp primrec_commandCode)

theorem primrec_commandMk [Primcodable P] [Primcodable Q] [Primcodable Γ]
    {q : P → Q} {a : P → Γ} {d : P → Move} (hq : Primrec q) (ha : Primrec a) (hd : Primrec d) :
    Primrec (fun p => (⟨q p,a p,d p⟩ : Command Q Γ)) :=
  Primrec.of_equiv_symm.comp (hq.pair (ha.pair hd))

variable [Fintype S] [Primcodable P] [Primcodable Q] [Primcodable Q']
theorem primrec_stateMap {f : P → Q → Q'} (hf : Primrec (fun x : P × Q => f x.1 x.2)) :
    Primrec (fun x : P × Simulator.Head S Q => stateMap (f x.1) x.2) := by
  exact (Primrec.sumCasesOn (primrec_simCode.comp Primrec.snd)
    (primrec_ofStatic.comp Primrec.snd).to₂
    (primrec_dynamic.comp ((Primrec.fst.comp Primrec.snd).pair
      (hf.comp ((Primrec.fst.comp Primrec.fst).pair (Primrec.snd.comp Primrec.snd))))).to₂).of_eq
        (fun x => by cases x.2 <;> rfl)

theorem primrec_controlMap {f : P → Q → Q'} (hf : Primrec (fun x : P × Q => f x.1 x.2)) :
    Primrec (fun x : P × Control.Head S Q => controlMap (f x.1) x.2) := by
  exact (Primrec.sumCasesOn (primrec_controlCode.comp Primrec.snd)
    (primrec_controlDecode.comp (Primrec.sumInl.comp Primrec.snd)).to₂
    (primrec_machine.comp ((primrec_stateMap hf).comp
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))).to₂).of_eq
        (fun x => by cases x.2 <;> rfl)

theorem primrec_instruction [Primcodable Γ] {q : P → Q} {t : P → Γ} {b : P → Bool}
    (hq : Primrec q) (ht : Primrec t) (hb : Primrec b) :
    Primrec (fun p => (⟨q p,t p,b p⟩ : Instruction Q Γ)) :=
  Primrec.of_equiv_symm.comp (hq.pair (ht.pair hb))

omit [Fintype S] [Primcodable P] [Primcodable Q] [Primcodable Q'] in
theorem stateMap_injective {f : Q → Q'} (hf : Function.Injective f) :
    Function.Injective (stateMap (S := S) f) := by
  intro a b h
  cases a <;> cases b <;> simp_all [stateMap]
  all_goals exact hf h

omit [Fintype S] [Primcodable P] [Primcodable Q] [Primcodable Q'] in
theorem controlMap_injective {f : Q → Q'} (hf : Function.Injective f) :
    Function.Injective (controlMap (S := S) f) := by
  intro a b h
  cases a <;> cases b <;> simp_all [controlMap]
  exact stateMap_injective hf h

end FiniteAlgebraicEnvelopes.Compiler.HeadCodec

namespace FiniteAlgebraicEnvelopes.Compiler.Simulator
open HeadCodec
variable {S Γ Q Q' : Type*} [DecidableEq Γ]
variable (A : Alphabet S Γ) (M : Machine Q Γ) (N : Machine Q' Γ) (i : Q → Q')
  (hi : N.initial=i M.initial)
  (ht : ∀ q a,N.transition (i q) a=(M.transition q a).map (commandMap i))

theorem table_direction_map (q : Head S Q) :
    (table A N).direction (stateMap i q)=(table A M).direction q := by
  cases q <;> rfl

theorem table_boundary_map (q : Head S Q) :
    (table A N).boundary (stateMap i q)=((table A M).boundary q).map (stateMap i) := by
  cases q <;> try rfl
  case scan r => cases r <;> rfl

include hi ht in
theorem table_cell_map (q : Head S Q) (b : Base S) (a : Tag S Γ) :
    (table A N).cell (stateMap i q) b a=
      ((table A M).cell q b a).map (Scan.mapInstruction (stateMap i)) := by
  cases q with
  | start | ok => rfl
  | rewind r => rfl
  | finish => rfl
  | left q => cases b <;> rfl
  | scan r =>
    cases r <;> cases b <;>
      simp [table,cell,stateMap,Scan.mapInstruction,hi]
    all_goals split <;> simp_all [Scan.mapInstruction,stateMap]
    all_goals split <;> simp_all [Scan.mapInstruction,stateMap,Option.map_map,Function.comp_def]
  | run q =>
    cases b <;> try rfl
    case workspace =>
      simp only [table,cell,stateMap,ht]
      cases h : M.transition q a.work with
      | none => rfl
      | some c =>
        rcases c with ⟨q,g,m⟩
        cases m <;> rfl

end FiniteAlgebraicEnvelopes.Compiler.Simulator

namespace FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open Simulator
open scoped HeadCodec
variable {S Γ Q P : Type*} [Fintype S] [Fintype Γ] [DecidableEq S] [DecidableEq Γ]
  [Primcodable Γ] [Primcodable Q] [Primcodable P]
variable (A : Alphabet S Γ) (M : P → Machine Q Γ)
  (hinit : Primrec (fun p => (M p).initial))
  (htrans : Primrec (fun x : P × Q × Γ => (M x.1).transition x.2.1 x.2.2))

def dummy : Machine Unit Γ := ⟨(),fun _ _ => none⟩

omit [Fintype S] [Fintype Γ] [DecidableEq S] [Primcodable Γ] [Primcodable Q] [Primcodable P] in
theorem static_cell (p : P) (s : Static S) (b : Base S) (t : Tag S Γ) :
    cell A (M p) (ofStatic s) b t=
      (cell A dummy (ofStatic s) b t).map
        (Scan.mapInstruction (stateMap (fun _ : Unit => (M p).initial))) := by
  cases s with
  | start | rewind | finish | ok => rfl
  | scan r =>
    cases r <;> cases b <;>
      simp [cell,ofStatic,stateMap,Scan.mapInstruction,dummy]
    all_goals split <;> simp_all [Scan.mapInstruction,stateMap]
    all_goals split <;> simp_all [Scan.mapInstruction,stateMap,Option.map_map,Function.comp_def]

include hinit in
omit [DecidableEq S] [Primcodable Γ] in
theorem primrec_staticCell : Primrec (fun x : P × Static S × Base S × Tag S Γ =>
    cell A (M x.1) (ofStatic x.2.1) x.2.2.1 x.2.2.2) := by
  have hc : Primrec (fun x : P × Static S × Base S × Tag S Γ =>
      cell A dummy (ofStatic x.2.1) x.2.2.1 x.2.2.2) :=
    (Primrec.dom_finite (fun y : Static S × Base S × Tag S Γ =>
      cell A dummy (ofStatic y.1) y.2.1 y.2.2)).comp Primrec.snd
  have hp := primrec_stateMap (S := S) (P := P) (Q := Unit) (Q' := Q)
    (f := fun p (_ : Unit) => (M p).initial) (hinit.comp Primrec.fst)
  have hs : Primrec₂ (fun (x : P × Static S × Base S × Tag S Γ)
      (c : Instruction (Simulator.Head S Unit) (Tag S Γ)) =>
      Scan.mapInstruction (stateMap (fun _ : Unit => (M x.1).initial)) c) :=
    (primrec_instruction (hp.comp ((Primrec.fst.comp Primrec.fst).pair
      (Instruction.primrec_head.comp Primrec.snd)))
      (Instruction.primrec_tag.comp Primrec.snd) (Instruction.primrec_cross.comp Primrec.snd)).to₂
  exact (Primrec.option_map hc hs).of_eq fun x => (static_cell A M x.1 x.2.1 x.2.2.1 x.2.2.2).symm

def leftCross : Base S → Option Bool
  | .workspace => some true | .cutC => some false | _ => none

omit [DecidableEq S] [Primcodable Γ] in
theorem primrec_leftCell : Primrec (fun x : P × Q × Base S × Tag S Γ =>
    cell A (M x.1) (.left x.2.1) x.2.2.1 x.2.2.2) := by
  have hc : Primrec (fun x : P × Q × Base S × Tag S Γ => leftCross x.2.2.1) :=
    (Primrec.dom_finite (leftCross (S := S))).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hs : Primrec₂ (fun (x : P × Q × Base S × Tag S Γ) (b : Bool) =>
      (⟨.run x.2.1,x.2.2.2,b⟩ : Instruction (Simulator.Head S Q) (Tag S Γ))) :=
    (primrec_instruction
      (primrec_dynamic.comp ((Primrec.const false).pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd).to₂
  exact (Primrec.option_map hc hs).of_eq fun x => by cases x.2.2.1 <;> rfl

include htrans in
omit [DecidableEq S] in
theorem primrec_runWorkspace : Primrec (fun x : P × Q × Tag S Γ =>
    cell A (M x.1) (.run x.2.1) .workspace x.2.2) := by
  have ht : Primrec (fun x : P × Q × Tag S Γ => x.2.2) := Primrec.snd.comp Primrec.snd
  have hw : Primrec (fun x : Tag S Γ => x.work) := Primrec.dom_finite _
  have hc := htrans.comp (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair (hw.comp ht)))
  have hz : Primrec (fun x : P × Q × Tag S Γ =>
      some (⟨.rewind .readout,x.2.2,false⟩ : Instruction (Simulator.Head S Q) (Tag S Γ))) :=
    Primrec.option_some.comp (primrec_instruction (Primrec.const _) ht (Primrec.const false))
  have hd : Primrec₂ (fun (x : P × Q × Tag S Γ) (c : Command Q Γ) =>
      some (⟨(if c.move = .left then .left c.state else .run c.state),
        {x.2.2 with work := c.write}, c.move == .right⟩ : Instruction (Simulator.Head S Q) (Tag S Γ))) := by
    unfold Primrec₂
    apply Primrec.option_some.comp
    apply primrec_instruction
    · exact (primrec_dynamic.comp
        (((Primrec.dom_finite (fun d : Move => decide (d=.left))).comp
          ((primrec_commandMove (Q := Q) (Γ := Γ)).comp Primrec.snd)).pair
            (primrec_commandState.comp Primrec.snd))).of_eq fun x => by
              simp only [dynamic, decide_eq_true_eq]
    · exact (Primrec.dom_finite (fun p : Tag S Γ × Γ => {p.1 with work := p.2})).comp
        ((ht.comp Primrec.fst).pair ((primrec_commandWrite (Q := Q) (Γ := Γ)).comp Primrec.snd))
    · exact (Primrec.dom_finite (fun d : Move => d == .right)).comp
        ((primrec_commandMove (Q := Q) (Γ := Γ)).comp Primrec.snd)
  exact (Primrec.option_casesOn hc hz hd).of_eq fun x => by
    simp only [cell]
    cases (M x.1).transition x.2.1 x.2.2.work <;> rfl

include htrans in
theorem primrec_runCell : Primrec (fun x : P × Q × Base S × Tag S Γ =>
    cell A (M x.1) (.run x.2.1) x.2.2.1 x.2.2.2) := by
  have hb : Primrec (fun x : P × Q × Base S × Tag S Γ => decide (x.2.2.1=.workspace)) :=
    (Primrec.dom_finite (fun b : Base S => decide (b=.workspace))).comp
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  exact (Primrec.cond hb
    ((primrec_runWorkspace A M htrans).comp (Primrec.fst.pair
      ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
    (Primrec.const none)).of_eq fun x => by cases x.2.2.1 <;> rfl

include hinit htrans in
theorem primrec_simCell : Primrec (fun x : P × Simulator.Head S Q × Base S × Tag S Γ =>
    (Simulator.table A (M x.1)).cell x.2.1 x.2.2.1 x.2.2.2) := by
  let X := P × Simulator.Head S Q × Base S × Tag S Γ
  have hp : Primrec (fun x : X => x.1) := Primrec.fst
  have hbt : Primrec (fun x : X => x.2.2) := Primrec.snd.comp Primrec.snd
  have hs : Primrec₂ (fun (x : X) (s : Static S) => cell A (M x.1) (ofStatic s) x.2.2.1 x.2.2.2) :=
    ((primrec_staticCell A M hinit).comp
      ((hp.comp Primrec.fst).pair (Primrec.snd.pair (hbt.comp Primrec.fst)))).to₂
  have hd : Primrec₂ (fun (x : X) (d : Bool × Q) => cell A (M x.1) (dynamic d) x.2.2.1 x.2.2.2) := by
    unfold Primrec₂
    exact (Primrec.cond (Primrec.fst.comp Primrec.snd)
      ((primrec_leftCell A M).comp ((hp.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.snd).pair (hbt.comp Primrec.fst))))
      ((primrec_runCell A M htrans).comp ((hp.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.snd).pair (hbt.comp Primrec.fst))))).of_eq fun x => by
          cases h : x.2.1 <;> simp [dynamic,h]
  exact (Primrec.sumCasesOn (primrec_simCode.comp (Primrec.fst.comp Primrec.snd)) hs hd).of_eq
    fun x => by cases x.2.1 <;> rfl

def staticBoundary : Static S → Option (Static S)
  | .start => some (.rewind .input) | .rewind r => some (.scan r)
  | .scan .input => some (.rewind .spare) | .finish => some .ok | _ => none

omit [Fintype Γ] [DecidableEq S] [Primcodable Γ] in
theorem primrec_simBoundary : Primrec (fun x : P × Simulator.Head S Q =>
    (Simulator.table A (M x.1)).boundary x.2) := by
  have hs : Primrec₂ (fun (_ : P × Simulator.Head S Q) (s : Static S) =>
      (staticBoundary s).map (ofStatic (Q := Q))) :=
    (Primrec.option_map ((Primrec.dom_finite (staticBoundary (S := S))).comp Primrec.snd)
      (primrec_ofStatic.comp Primrec.snd).to₂).to₂
  exact (Primrec.sumCasesOn (primrec_simCode.comp Primrec.snd) hs (Primrec.const none).to₂).of_eq
    fun x => by
      cases x.2 <;> simp [simCode,table,staticBoundary,ofStatic]
      rename_i r; cases r <;> rfl

omit [Fintype Γ] [DecidableEq S] [Primcodable Γ] in
theorem primrec_simDirection : Primrec (fun x : P × Simulator.Head S Q =>
    decide ((Simulator.table A (M x.1)).direction x.2 = .right)) := by
  have hs : Primrec₂ (fun (_ : P × Simulator.Head S Q) (s : Static S) =>
      decide ((Simulator.table A dummy).direction (ofStatic s) = .right)) :=
    ((Primrec.dom_finite (fun s : Static S =>
      decide ((Simulator.table A dummy).direction (ofStatic s) = .right))).comp Primrec.snd).to₂
  exact (Primrec.sumCasesOn (primrec_simCode.comp Primrec.snd) hs
    (Primrec.not.comp (Primrec.fst.comp Primrec.snd)).to₂).of_eq
      fun x => by cases x.2 <;> rfl

def staticControl (k : Fin 5) : Control.Head S Q := controlCode.symm (.inl k)

omit [Fintype S] [DecidableEq S] [Primcodable Q] in
theorem validatorHead_map {Q' : Type*} (f : Q → Q') (h : Validator.Head) :
    controlMap (S := S) f (Control.validatorHead h)=Control.validatorHead h := by
  cases h <;> rfl

omit [Fintype S] [Fintype Γ] [Primcodable Γ] [Primcodable Q] [Primcodable P] in
theorem staticControl_cell (p : P) (k : Fin 5) (b : Base S) (t : Tag S Γ) :
    (Control.table A (M p)).cell (staticControl k) b t =
      ((Control.table A dummy).cell (staticControl k) b t).map
        (Scan.mapInstruction (controlMap (fun _ : Unit => (M p).initial))) := by
  have hm :
      Scan.mapInstruction (T := Tag S Γ) (controlMap (fun _ : Unit => (M p).initial)) ∘
        Scan.mapInstruction (Control.validatorHead (S := S)) =
          Scan.mapInstruction (Control.validatorHead (S := S) (Q := Q)) := by
    funext c
    cases c with | mk q t b => simp [Scan.mapInstruction,validatorHead_map]
  fin_cases k <;>
    simp [staticControl,controlCode,Control.table,Control.toValidator,Option.map_map,hm]

omit [Fintype S] [Fintype Γ] [Primcodable Γ] [Primcodable Q] [Primcodable P] in
theorem staticControl_boundary (p : P) (k : Fin 5) :
    (Control.table A (M p)).boundary (staticControl k) =
      ((Control.table A dummy).boundary (staticControl k)).map
        (controlMap (fun _ : Unit => (M p).initial)) := by
  have hm : controlMap (fun _ : Unit => (M p).initial) ∘
      Control.validatorHead (S := S) = Control.validatorHead (S := S) (Q := Q) := by
    funext q; exact validatorHead_map _ q
  fin_cases k <;>
    simp [staticControl,controlCode,Control.table,Control.toValidator,Option.map_map,hm]

include hinit in
omit [Primcodable Γ] in
theorem primrec_controlStaticCell : Primrec (fun x : P × Fin 5 × Base S × Tag S Γ =>
    (Control.table A (M x.1)).cell (staticControl x.2.1) x.2.2.1 x.2.2.2) := by
  have hc : Primrec (fun x : P × Fin 5 × Base S × Tag S Γ =>
      (Control.table A dummy).cell (staticControl x.2.1) x.2.2.1 x.2.2.2) :=
    (Primrec.dom_finite (fun y : Fin 5 × Base S × Tag S Γ =>
      (Control.table A dummy).cell (staticControl y.1) y.2.1 y.2.2)).comp Primrec.snd
  have hp := primrec_controlMap (S := S) (P := P) (Q := Unit) (Q' := Q)
    (f := fun p (_ : Unit) => (M p).initial) (hinit.comp Primrec.fst)
  have hs : Primrec₂ (fun (x : P × Fin 5 × Base S × Tag S Γ)
      (c : Instruction (Control.Head S Unit) (Tag S Γ)) =>
      Scan.mapInstruction (controlMap (fun _ : Unit => (M x.1).initial)) c) :=
    (primrec_instruction (hp.comp ((Primrec.fst.comp Primrec.fst).pair
      (Instruction.primrec_head.comp Primrec.snd)))
      (Instruction.primrec_tag.comp Primrec.snd) (Instruction.primrec_cross.comp Primrec.snd)).to₂
  exact (Primrec.option_map hc hs).of_eq fun x => (staticControl_cell A M x.1 x.2.1 x.2.2.1 x.2.2.2).symm

include hinit htrans in
theorem primrec_controlCell : Primrec (fun x : P × Control.Head S Q × Base S × Tag S Γ =>
    (Control.table A (M x.1)).cell x.2.1 x.2.2.1 x.2.2.2) := by
  let X := P × Control.Head S Q × Base S × Tag S Γ
  have hp : Primrec (fun x : X => x.1) := Primrec.fst
  have hbt : Primrec (fun x : X => x.2.2) := Primrec.snd.comp Primrec.snd
  have hs := ((primrec_controlStaticCell A M hinit).comp
    ((hp.comp Primrec.fst).pair (Primrec.snd.pair (hbt.comp Primrec.fst)))).to₂
  have hd : Primrec₂ (fun (x : X) (q : Simulator.Head S Q) =>
      ((Simulator.table A (M x.1)).cell q x.2.2.1 x.2.2.2).map
        (Scan.mapInstruction Control.Head.machine)) := by
    unfold Primrec₂
    apply Primrec.option_map ((primrec_simCell A M hinit htrans).comp
      ((hp.comp Primrec.fst).pair (Primrec.snd.pair (hbt.comp Primrec.fst))))
    exact (primrec_instruction (primrec_machine.comp (Instruction.primrec_head.comp Primrec.snd))
      (Instruction.primrec_tag.comp Primrec.snd) (Instruction.primrec_cross.comp Primrec.snd)).to₂
  exact (Primrec.sumCasesOn (primrec_controlCode.comp (Primrec.fst.comp Primrec.snd)) hs hd).of_eq
    fun x => by cases x.2.1 <;> rfl

include hinit in
omit [Fintype Γ] [Primcodable Γ] in
theorem primrec_controlBoundary : Primrec (fun x : P × Control.Head S Q =>
    (Control.table A (M x.1)).boundary x.2) := by
  have hp := primrec_controlMap (S := S) (P := P) (Q := Unit) (Q' := Q)
    (f := fun p (_ : Unit) => (M p).initial) (hinit.comp Primrec.fst)
  have hs : Primrec₂ (fun (x : P × Control.Head S Q) (k : Fin 5) =>
      (Control.table A (M x.1)).boundary (staticControl k)) := by
    unfold Primrec₂
    exact (Primrec.option_map
      ((Primrec.dom_finite (fun k : Fin 5 => (Control.table A dummy).boundary (staticControl k))).comp Primrec.snd)
      (hp.comp ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair Primrec.snd)).to₂).of_eq
        fun x => (staticControl_boundary A M x.1.1 x.2).symm
  have hd : Primrec₂ (fun (x : P × Control.Head S Q) (q : Simulator.Head S Q) =>
      ((Simulator.table A (M x.1)).boundary q).map Control.Head.machine) :=
    (Primrec.option_map ((primrec_simBoundary A M).comp
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))
        (primrec_machine.comp Primrec.snd).to₂).to₂
  exact (Primrec.sumCasesOn (primrec_controlCode.comp Primrec.snd) hs hd).of_eq
    fun x => by cases x.2 <;> rfl

omit [Fintype Γ] [Primcodable Γ] in
theorem primrec_controlDirection : Primrec (fun x : P × Control.Head S Q =>
    decide ((Control.table A (M x.1)).direction x.2 = .right)) := by
  have hs : Primrec₂ (fun (_ : P × Control.Head S Q) (k : Fin 5) =>
      decide ((Control.table A dummy).direction (staticControl k) = .right)) :=
    ((Primrec.dom_finite (fun k : Fin 5 =>
      decide ((Control.table A dummy).direction (staticControl k) = .right))).comp Primrec.snd).to₂
  exact (Primrec.sumCasesOn (primrec_controlCode.comp Primrec.snd) hs
    ((primrec_simDirection A M).comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂).of_eq
      fun x => by cases x.2 <;> rfl

end FiniteAlgebraicEnvelopes.Compiler.HeadCodec

namespace FiniteAlgebraicEnvelopes.Compiler.Control
open HeadCodec
variable {S Γ Q Q' : Type*} [DecidableEq S] [DecidableEq Γ] [Fintype S]
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ) (N : Simulator.Machine Q' Γ)
  (i : Q → Q') (hi : N.initial=i M.initial)
  (ht : ∀ q a,N.transition (i q) a=(M.transition q a).map (commandMap i))

omit [Fintype S] in
theorem table_direction_map (q : Head S Q) :
    (table A N).direction (controlMap i q)=(table A M).direction q := by
  cases q <;> try rfl
  exact Simulator.table_direction_map A M N i _

omit [Fintype S] in
theorem table_boundary_map (q : Head S Q) :
    (table A N).boundary (controlMap i q)=((table A M).boundary q).map (controlMap i) := by
  have hm : controlMap i ∘ validatorHead (S := S)=validatorHead (S := S) := by
    funext q; cases q <;> rfl
  cases q <;> simp only [table,controlMap,toValidator,Option.map_map]
  all_goals try { simp only [hm] }
  case machine q =>
    rw [Simulator.table_boundary_map A M N i]
    simp only [Option.map_map]
    rfl

include hi ht in
omit [Fintype S] in
theorem table_cell_map (q : Head S Q) (b : Base S) (a : Tag S Γ) :
    (table A N).cell (controlMap i q) b a=
      ((table A M).cell q b a).map (Scan.mapInstruction (controlMap i)) := by
  have hm : Scan.mapInstruction (T := Tag S Γ) (controlMap i) ∘
      Scan.mapInstruction (validatorHead (S := S))=Scan.mapInstruction (validatorHead (S := S)) := by
    funext c
    cases c with | mk h t b => cases h <;> rfl
  cases q <;> simp only [table,controlMap,toValidator,Option.map_map]
  all_goals try { simp only [hm] }
  case machine q =>
    rw [Simulator.table_cell_map A M N i hi ht]
    simp only [Option.map_map]
    rfl

omit [DecidableEq S] [DecidableEq Γ] [Fintype S] in
theorem entry_map (blank : Γ) (v : Sector S Γ Q) :
    Entry blank (Scan.mapHead (controlMap i) v) ↔ Entry blank v := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> simp [Entry,Scan.mapHead,controlMap]

omit [DecidableEq S] [DecidableEq Γ] [Fintype S] in
theorem success_map (v : Sector S Γ Q) :
    Success (Scan.mapHead (controlMap i) v) ↔ Success v := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> simp [Success,Scan.mapHead,controlMap]
  case machine q => cases q <;> simp [stateMap]
end FiniteAlgebraicEnvelopes.Compiler.Control

namespace FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open FiniteAlgebraicEnvelopes.Effect
open scoped HeadCodec
variable {S Q : Type*} [Fintype S]

noncomputable def simSupport (qs : List Q) : List (Simulator.Head S Q) :=
  (Scan.finiteList (Static S)).map ofStatic ++ qs.flatMap (fun q => [.run q,.left q])
noncomputable def controlSupport (qs : List Q) : List (Control.Head S Q) :=
  (Scan.finiteList (Fin 5)).map staticControl ++ (simSupport qs).map Control.Head.machine

@[simp] theorem mem_simSupport (qs : List Q) (h : Simulator.Head S Q) :
    h∈simSupport qs ↔ match h with | .run q | .left q => q∈qs | _ => True := by
  cases h <;> simp [simSupport,ofStatic]
  case start => exact ⟨.start,rfl⟩
  case rewind r => exact ⟨.rewind r,rfl⟩
  case scan r => exact ⟨.scan r,rfl⟩
  case finish => exact ⟨.finish,rfl⟩
  case ok => exact ⟨.ok,rfl⟩
  case run q => intro a ha; cases a <;> cases ha
  case left q => intro a ha; cases a <;> cases ha

@[simp] theorem mem_controlSupport (qs : List Q) (h : Control.Head S Q) :
    h∈controlSupport qs ↔ match h with | .machine (.run q) | .machine (.left q) => q∈qs | _ => True := by
  cases h <;> simp only [controlSupport,List.mem_append,List.mem_map,Scan.mem_finiteList,true_and]
  case initial => exact iff_true_intro (Or.inl ⟨0,rfl⟩)
  case left => exact iff_true_intro (Or.inl ⟨1,rfl⟩)
  case right => exact iff_true_intro (Or.inl ⟨2,rfl⟩)
  case workspace => exact iff_true_intro (Or.inl ⟨3,rfl⟩)
  case suffix => exact iff_true_intro (Or.inl ⟨4,rfl⟩)
  case machine h =>
    have hn : ¬∃ a,staticControl a=Control.Head.machine h := by
      rintro ⟨a,ha⟩; fin_cases a <;> cases ha
    simp only [hn,false_or,Control.Head.machine.injEq,exists_eq_right,mem_simSupport]
    cases h <;> rfl

variable [Primcodable Q]
theorem primrec_simSupport : Primrec (simSupport (S := S) (Q := Q)) := by
  have hr : Primrec (Simulator.Head.run (S := S) (Q := Q)) :=
    primrec_dynamic.comp ((Primrec.const false).pair Primrec.id)
  have hl : Primrec (Simulator.Head.left (S := S) (Q := Q)) :=
    primrec_dynamic.comp ((Primrec.const true).pair Primrec.id)
  exact Primrec.list_append.comp (Primrec.const _)
    (Primrec.list_flatMap Primrec.id ((Primrec.list_cons.comp hr
      (Primrec.list_cons.comp hl (Primrec.const []))).comp Primrec.snd).to₂)

theorem primrec_controlSupport : Primrec (controlSupport (S := S) (Q := Q)) :=
  Primrec.list_append.comp (Primrec.const _)
    (Primrec.list_map primrec_simSupport (primrec_machine.comp Primrec.snd).to₂)

end FiniteAlgebraicEnvelopes.Compiler.HeadCodec

namespace FiniteAlgebraicEnvelopes.Compiler
open FiniteAlgebraicEnvelopes.Effect
namespace Surface.Uniform
open Surface HeadCodec
open scoped HeadCodec
open Scan
variable {S Γ H : Type*} [Fintype S] [Fintype Γ] [Primcodable H]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq H] (blank : Γ)

omit [Fintype S] [Fintype Γ] [Primcodable H] [DecidableEq H] in
 theorem rawSweep_takeDrop (l r : Cells S Γ) (lb rb : Bool) :
    rawSweep (H := H) blank l r lb rb =
      ⟨l.dropWhile (cleanAnchor blank),.raw,
        (l.takeWhile (cleanAnchor blank)).reverse ++ r,lb,rb⟩ := by
  induction l generalizing r with
  | nil => rfl
  | cons c l ih =>
    rcases c with ⟨b,t⟩
    cases b with
    | anchor a =>
      by_cases h : t = clean blank
      · simp [rawSweep,h,cleanAnchor,ih,List.reverse_cons,List.append_assoc]
      · simp [rawSweep,h,cleanAnchor]
    | cutC | cutD | workspace => simp [rawSweep,cleanAnchor]

omit [DecidableEq H] in
 theorem primrec_rawSweep : Primrec (fun p : (Cells S Γ × Cells S Γ) × Bool × Bool =>
    rawSweep (H := H) blank p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hp := Primrec.dom_finite (cleanAnchor (S := S) blank)
  exact (Scan.Sector.primrec_mk
    ((Primrec.list_dropWhile hp).comp (Primrec.fst.comp Primrec.fst))
    (Primrec.const Head.raw)
    (Primrec.list_append.comp
      (Primrec.list_reverse.comp ((Primrec.list_takeWhile hp).comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.fst))
    (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).of_eq
      fun p => (rawSweep_takeDrop blank _ _ _ _).symm

 theorem primrec_rawNormal : Primrec (rawNormal (S := S) (H := H) blank) := by
  have hg : PrimrecPred (fun v : Sector S Γ H => v.head = .raw) :=
    Primrec.eq.comp Scan.Sector.primrec_head (Primrec.const Head.raw)
  have hh : Primrec (fun v : Sector S Γ H => if v.head = .raw then
      rawSweep blank v.left v.right v.leftBoundary v.rightBoundary else v) :=
    Primrec.ite hg ((primrec_rawSweep blank).comp
      ((Scan.Sector.primrec_left.pair Scan.Sector.primrec_right).pair
        (Scan.Sector.primrec_lb.pair Scan.Sector.primrec_rb))) Primrec.id
  exact hh.of_eq fun v => by cases h : v.head <;> simp [rawNormal,h]

 theorem primrec_trimQuota : Primrec (trimQuota (S := S) blank) :=
  (Primrec.list_dropWhile (Primrec.dom_finite _)).of_eq fun l => (trimQuota_drop blank l).symm

 theorem primrec_quotaNormal : Primrec (quotaNormal (S := S) (H := H) blank) := by
  have hg : PrimrecPred (fun v : Sector S Γ H =>
      v.head = .pending ∧ v.right.head? = some (Validator.cell blank .cutD)) :=
    (Primrec.eq.comp Scan.Sector.primrec_head (Primrec.const Head.pending)).and
      (Primrec.eq.comp (Primrec.list_head?.comp Scan.Sector.primrec_right) (Primrec.const _))
  have hh : Primrec (fun v : Sector S Γ H =>
      if v.head = .pending ∧ v.right.head? = some (Validator.cell blank .cutD)
      then {v with left := trimQuota blank v.left} else v) :=
    Primrec.ite hg
      (Scan.Sector.primrec_mk ((primrec_trimQuota blank).comp Scan.Sector.primrec_left)
        Scan.Sector.primrec_head Scan.Sector.primrec_right Scan.Sector.primrec_lb Scan.Sector.primrec_rb)
      Primrec.id
  exact hh.of_eq fun v => by
    rcases v with ⟨l,q,r,lb,rb⟩
    cases q <;> cases r <;> simp [quotaNormal]

 theorem primrec_unmerge : Primrec (unmerge (S := S) (H := H) blank) := by
  have hg : PrimrecPred (fun v : Sector S Γ H =>
      v.head = .pending ∧ v.left.head? = some (Validator.cell blank .cutC) ∧
        v.right.head? = some (Validator.cell blank .cutD)) :=
    (Primrec.eq.comp Scan.Sector.primrec_head (Primrec.const Head.pending)).and
      ((Primrec.eq.comp (Primrec.list_head?.comp Scan.Sector.primrec_left) (Primrec.const _)).and
        (Primrec.eq.comp (Primrec.list_head?.comp Scan.Sector.primrec_right) (Primrec.const _)))
  have hl : Primrec (fun v : Sector S Γ H => rawNormal (H := H) blank
      ⟨v.left.tail,.raw,[],v.leftBoundary,true⟩) :=
    (primrec_rawNormal (H := H) blank).comp (Scan.Sector.primrec_mk
      (Primrec.list_tail.comp Scan.Sector.primrec_left) (Primrec.const Head.raw)
      (Primrec.const []) Scan.Sector.primrec_lb (Primrec.const true))
  have hr : Primrec (fun v : Sector S Γ H => rawNormal (H := H) blank
      ⟨[],.raw,v.right.tail,true,v.rightBoundary⟩) :=
    (primrec_rawNormal (H := H) blank).comp (Scan.Sector.primrec_mk (Primrec.const [])
      (Primrec.const Head.raw) (Primrec.list_tail.comp Scan.Sector.primrec_right)
      (Primrec.const true) Scan.Sector.primrec_rb)
  have hh : Primrec (fun v : Sector S Γ H =>
      if v.head = .pending ∧ v.left.head? = some (Validator.cell blank .cutC) ∧
        v.right.head? = some (Validator.cell blank .cutD)
      then [rawNormal blank ⟨v.left.tail,.raw,[],v.leftBoundary,true⟩,
        rawNormal blank ⟨[],.raw,v.right.tail,true,v.rightBoundary⟩]
      else [v]) :=
    Primrec.ite hg (Primrec.list_cons.comp hl
      (Primrec.list_cons.comp hr (Primrec.const [])))
      (Primrec.list_cons.comp Primrec.id (Primrec.const []))
  exact hh.of_eq fun v => by
    rcases v with ⟨l,q,r,lb,rb⟩
    cases l with
    | nil => cases q <;> simp [unmerge]
    | cons c l =>
      cases r with
      | nil => cases q <;> simp [unmerge]
      | cons d r => cases q <;> simp [unmerge]

 theorem primrec_pendingPreprocess : Primrec (pendingPreprocess (S := S) (H := H) blank) :=
  (primrec_unmerge blank).comp (primrec_quotaNormal blank)
omit [DecidableEq S] [DecidableEq Γ] in
 theorem primrec_cleanupNormal : Primrec (cleanupNormal (S := S) (H := H) blank) := by
  have hg : PrimrecPred (fun v : Sector S Γ H => v.head = .cleanup) :=
    Primrec.eq.comp Scan.Sector.primrec_head (Primrec.const Head.cleanup)
  have hh : Primrec (fun v : Sector S Γ H => if v.head = .cleanup then
      (⟨[],if v.leftBoundary then .raw else .cleanup,
        Cleanup.output blank v.left.reverse ++ v.right,v.leftBoundary,v.rightBoundary⟩ : Sector S Γ H)
      else v) :=
    Primrec.ite hg (Scan.Sector.primrec_mk (Primrec.const [])
      ((Primrec.dom_finite (fun b : Bool => if b then (Head.raw : Head H) else .cleanup)).comp
        Scan.Sector.primrec_lb)
      (Primrec.list_append.comp ((primrec_cleanupOutput blank).comp
        (Primrec.list_reverse.comp Scan.Sector.primrec_left)) Scan.Sector.primrec_right)
      Scan.Sector.primrec_lb Scan.Sector.primrec_rb) Primrec.id
  exact hh.of_eq fun v => by
    rcases v with ⟨l,q,r,lb,rb⟩
    cases q <;> cases lb <;> rfl

 theorem primrec_cleanupPreprocess : Primrec (cleanupPreprocess (S := S) (H := H) blank) :=
  (primrec_rawNormal blank).comp (primrec_cleanupNormal blank)
end Surface.Uniform
end FiniteAlgebraicEnvelopes.Compiler

end OAI
