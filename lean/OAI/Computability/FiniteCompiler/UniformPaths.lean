import OAI.Computability.FiniteCompiler.UniformControl

namespace OAI

/-!
Uniform surface and path normalization with recursive compiler interfaces.
-/

namespace FiniteAlgebraicEnvelopes.Effect
variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]
theorem primrec_sumElim {f : α → γ} {g : β → γ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (Sum.elim f g) := by
  exact (Primrec.sumCasesOn Primrec.id (hf.comp Primrec.snd).to₂
    (hg.comp Primrec.snd).to₂).of_eq fun x => by cases x <;> rfl
end FiniteAlgebraicEnvelopes.Effect

namespace FiniteAlgebraicEnvelopes.Compiler.Path.Uniform
open FiniteAlgebraicEnvelopes.Compiler.Path HeadCodec FiniteAlgebraicEnvelopes.Effect
open scoped HeadCodec
variable {C H : Type*} [Primcodable C] [Primcodable H]

theorem primrec_left : Primrec (Letter.left (C := C) (H := H)) :=
  primrec_pathDecode.comp (Primrec.sumInr.comp Primrec.sumInl)
theorem primrec_right : Primrec (Letter.right (C := C) (H := H)) :=
  primrec_pathDecode.comp (Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.sumInl))
theorem primrec_head : Primrec (Letter.head (C := C) (H := H)) :=
  primrec_pathDecode.comp (Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.sumInr))

theorem primrec_typeOf : Primrec (typeOf (C := C) (H := H)) := by
  let f : Fin 3 → Shape := fun k => if k=0 then .zero else if k=1 then .path .outer .left else .path .right .outer
  exact ((primrec_sumElim (Primrec.dom_finite f)
    (primrec_sumElim (Primrec.const (Shape.path .left .left))
      (primrec_sumElim (Primrec.const (Shape.path .right .right)) (Primrec.const (Shape.path .left .right))))).comp
        primrec_pathCode).of_eq fun a => by cases a <;> rfl

theorem primrec_shape : Primrec (shape (C := C) (H := H)) := by
  have hp : Primrec (fun p : Letter C H × Shape => typeOf p.1 * p.2) :=
    (Primrec.dom_finite (fun p : Shape × Shape => p.1*p.2)).comp
      ((primrec_typeOf.comp Primrec.fst).pair Primrec.snd)
  exact (Primrec.list_foldr Primrec.id (Primrec.const Shape.unit)
    (hp.comp Primrec.snd).to₂).of_eq fun w => by
      induction w with
      | nil => rfl
      | cons a w ih => simpa only [id_eq,List.foldr_cons,shape_cons] using congrArg (typeOf a * ·) ih

theorem primrec_head? : Primrec (fun a : Letter C H => match a with | .head q => some q | _ => none) := by
  exact ((primrec_sumElim (Primrec.const none)
    (primrec_sumElim (Primrec.const none)
      (primrec_sumElim (Primrec.const none) Primrec.option_some))).comp primrec_pathCode).of_eq
        fun a => by cases a <;> rfl

theorem primrec_left? : Primrec (fun a : Letter C H => match a with | .left c => some c | _ => none) := by
  exact ((primrec_sumElim (Primrec.const none)
    (primrec_sumElim Primrec.option_some (Primrec.const none))).comp primrec_pathCode).of_eq
        fun a => by cases a <;> rfl

theorem primrec_right? : Primrec (fun a : Letter C H => match a with | .right c => some c | _ => none) := by
  exact ((primrec_sumElim (Primrec.const none)
    (primrec_sumElim (Primrec.const none)
      (primrec_sumElim Primrec.option_some (Primrec.const none)))).comp primrec_pathCode).of_eq
        fun a => by cases a <;> rfl

theorem primrec_heads : Primrec (heads (C := C) (H := H)) :=
  Primrec.listFilterMap Primrec.id (primrec_head?.comp Primrec.snd).to₂
theorem primrec_lefts : Primrec (lefts (C := C) (H := H)) :=
  Primrec.listFilterMap Primrec.id (primrec_left?.comp Primrec.snd).to₂
theorem primrec_rights : Primrec (rights (C := C) (H := H)) :=
  Primrec.listFilterMap Primrec.id (primrec_right?.comp Primrec.snd).to₂
 theorem primrec_encode : Primrec (encode (C := C) (H := H)) := by
  have hl : Primrec (fun v : Sector C H => v.left.reverse.map (Letter.left : C → Letter C H)) :=
    Primrec.list_map (Primrec.list_reverse.comp Sector.primrec_left)
      (primrec_left.comp Primrec.snd).to₂
  have hr : Primrec (fun v : Sector C H => v.right.map (Letter.right : C → Letter C H)) :=
    Primrec.list_map Sector.primrec_right (primrec_right.comp Primrec.snd).to₂
  exact Primrec.list_append.comp (Primrec.list_append.comp (Primrec.list_append.comp
    (Primrec.list_append.comp
      ((Primrec.dom_finite (fun b : Bool => if b then ([.enter] : List (Letter C H)) else [])).comp
        Sector.primrec_lb) hl)
      (Primrec.list_cons.comp (primrec_head.comp Sector.primrec_head) (Primrec.const []))) hr)
    ((Primrec.dom_finite (fun b : Bool => if b then ([.leave] : List (Letter C H)) else [])).comp
      Sector.primrec_rb)

 theorem primrec_glue : Primrec₂ (glue (C := C) (H := H)) := by
  have hn : Primrec (fun p : List (Letter C H) × List (List (Letter C H)) =>
      if p.1 = [] then [] else [p.1]) :=
    Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const [])) (Primrec.const [])
      (Primrec.list_cons.comp Primrec.fst (Primrec.const []))
  have hc : Primrec₂ (fun (p : List (Letter C H) × List (List (Letter C H)))
      (ct : List (Letter C H) × List (List (Letter C H))) => (p.1++ct.1)::ct.2) :=
    (Primrec.list_cons.comp (Primrec.list_append.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_casesOn Primrec.snd hn hc).to₂.of_eq fun u w => by
    cases w <;> cases u <;> rfl

variable [DecidableEq C] [DecidableEq H]

omit [Primcodable C] [Primcodable H] in
 theorem cuts_fold (w : List (Letter C H)) :
    cuts w = w.foldr (fun a cs => if a = .leave then [.leave]::cs else glue [a] cs) [] := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [cuts,ih]

 theorem primrec_cuts : Primrec (cuts (C := C) (H := H)) := by
  exact (Primrec.list_foldr Primrec.id (Primrec.const [])
    (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const Letter.leave))
      (Primrec.list_cons.comp (Primrec.const [Letter.leave]) (Primrec.snd.comp Primrec.snd))
      (primrec_glue.comp (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.const []))
        (Primrec.snd.comp Primrec.snd))).to₂).of_eq fun w => (cuts_fold w).symm

omit [DecidableEq C] [DecidableEq H] in
 theorem primrec_mem (a : Letter C H) : PrimrecPred (fun w : List (Letter C H) => a ∈ w) := by
  exact ((Primrec.eq.comp Primrec.id (Primrec.const a)).exists_mem_list).of_eq fun w => by simp

 theorem primrec_decode : Primrec (decode (C := C) (H := H)) := by
  let make : List (Letter C H) × H → Sector C H := fun p =>
    ⟨(lefts p.1).reverse,p.2,rights p.1,decide (.enter ∈ p.1),decide (.leave ∈ p.1)⟩
  have hm : Primrec make := Sector.primrec_mk
    (Primrec.list_reverse.comp (primrec_lefts.comp Primrec.fst)) Primrec.snd
    (primrec_rights.comp Primrec.fst) ((primrec_mem .enter).decide.comp Primrec.fst)
    ((primrec_mem .leave).decide.comp Primrec.fst)
  have ht : Primrec (fun p : List (Letter C H) × H =>
      if encode (make p) = p.1 then some (make p) else none) :=
    Primrec.ite (Primrec.eq.comp (primrec_encode.comp hm) Primrec.fst)
      (Primrec.option_some.comp hm) (Primrec.const none)
  have hh : Primrec (fun w : List (Letter C H) => if (heads w).length = 1 then
      (heads w).head?.bind (fun q => if encode (make (w,q)) = w then some (make (w,q)) else none)
      else none) :=
    Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp primrec_heads) (Primrec.const 1))
      (Primrec.option_bind (Primrec.list_head?.comp primrec_heads) ht.to₂) (Primrec.const none)
  exact hh.of_eq fun w => by
    unfold decode
    cases h : heads w with
    | nil => simp
    | cons q t => cases t with
      | nil => simp only [List.length_singleton,↓reduceIte,List.head?_cons,Option.bind_some]; rfl
      | cons q' t => simp

 theorem primrec_prepareChunk {P : Sector C H → List (Sector C H)} (hP : Primrec P) :
    Primrec (prepareChunk P) := by
  exact (Primrec.option_casesOn primrec_decode (Primrec.list_cons.comp Primrec.id (Primrec.const []))
    (Primrec.list_map (hP.comp Primrec.snd) (primrec_encode.comp Primrec.snd).to₂).to₂).of_eq
      fun w => by cases h : decode w <;> simp [prepareChunk,h]

 theorem primrec_prepareChunks {P : Sector C H → List (Sector C H)} (hP : Primrec P) :
    Primrec (prepareChunks P) :=
  Primrec.list_flatMap Primrec.id ((primrec_prepareChunk hP).comp Primrec.snd).to₂

 theorem primrec_prepare {P : Sector C H → List (Sector C H)} (hP : Primrec P) :
    Primrec (prepare P) :=
  (primrec_prepareChunks hP).comp primrec_cuts

end FiniteAlgebraicEnvelopes.Compiler.Path.Uniform

namespace FiniteAlgebraicEnvelopes.Effect.Graph
variable {α β : Type*}
variable (i : α → β) (r : α → α → Bool) (s : β → β → Bool)
variable (h : ∀ a b,s (i a) (i b)=r a b)

include h in
theorem expand_map (u v : List α) : expand s (u.map i) (v.map i)=(expand r u v).map i := by
  simp only [expand,List.map_append,List.any_map]
  rw [List.filter_map]
  simp only [Function.comp_def,h]

include h in
theorem search_map (u : List α) (a : α) (n : ℕ) :
    search s (u.map i) (i a) n=(search r u a n).map i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [search,ih,expand_map i r s h,←search]

include h in
theorem component_map (u : List α) (a : α) :
    component s (u.map i) (i a)=(component r u a).map i := by
  simp only [component,List.length_map,search_map i r s h]

end FiniteAlgebraicEnvelopes.Effect.Graph

namespace FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {H H' B T : Type*} [Fintype B] [Fintype T]

theorem sectorList_map (i : H → H') (heads : List H) (n : ℕ) :
    sectorList (B := B) (T := T) (heads.map i) n=
      (sectorList heads n).map (mapHead i) := by
  simp only [sectorList,List.flatMap_map,List.map_flatMap]
  rfl

variable [DecidableEq H] [DecidableEq H'] [DecidableEq B] [DecidableEq T]
omit [DecidableEq H] [DecidableEq H'] [DecidableEq T] in
theorem universeList_map (i : H → H') (heads : List H) (v : Sector H B T) :
    universeList (heads.map i) (mapHead i v)=(universeList heads v).map (mapHead i) := by
  simp only [universeList,mapHead,sectorList_map,List.filter_map,baseSkeleton]
  rfl

variable (i : H → H') (hi : Function.Injective i)
  (t : Table H B T) (u : Table H' B T)
  (hd : ∀ q,u.direction (i q)=t.direction q)
  (hc : ∀ q b a,u.cell (i q) b a=(t.cell q b a).map (mapInstruction i))
  (hb : ∀ q,u.boundary (i q)=(t.boundary q).map i)

omit [Fintype B] [Fintype T] [DecidableEq H] [DecidableEq H'] [DecidableEq B] [DecidableEq T] in
include hd hc hb in
theorem step_map (v : Sector H B T) :
    step u (mapHead i v)=(step t v).map (mapHead i) := by
  apply step_mapHead
  · exact hd _
  · exact hc _
  · exact hb _

omit [Fintype B] [Fintype T] [DecidableEq H] [DecidableEq H'] [DecidableEq B] [DecidableEq T] in
include hi in
theorem mapHead_injective : Function.Injective (mapHead (B := B) (T := T) i) := by
  intro v w hh
  cases v; cases w
  simp only [mapHead,Sector.mk.injEq] at hh ⊢
  exact ⟨hh.1,hi hh.2.1,hh.2.2⟩

omit [Fintype B] [Fintype T] in
include hi hd hc hb in
theorem stepBool_map (v w : Sector H B T) :
    decide (step u (mapHead i v)=some (mapHead i w))=decide (step t v=some w) := by
  rw [step_map i t u hd hc hb]
  have he : (step t v).map (mapHead i)=some (mapHead i w) ↔ step t v=some w := by
    rw [Option.map_eq_some_iff]
    constructor
    · rintro ⟨a,ha,he⟩
      exact (mapHead_injective i hi he) ▸ ha
    · intro he
      exact ⟨w,he,rfl⟩
  simp only [he]

include hi hd hc hb in
theorem componentList_map (heads : List H) (v : Sector H B T) :
    componentList (fun _ : Unit => u) (fun _ => heads.map i) ((),mapHead i v)=
      (componentList (fun _ : Unit => t) (fun _ => heads) ((),v)).map (mapHead i) := by
  rw [componentList,componentList,universeList_map]
  exact component_map _ _ _ (stepBool_map i hi t u hd hc hb) _ _

end FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform

namespace FiniteAlgebraicEnvelopes.Effect.Graph
variable {α : Type*} [DecidableEq α]

theorem expand_ext_universe (r : α → α → Bool) {u v s t : List α}
    (hu : u.toFinset=v.toFinset) (hs : s.toFinset=t.toFinset) :
    (expand r u s).toFinset=(expand r v t).toFinset := by
  have huu : ∀ a,a∈u ↔ a∈v := fun a => by simpa using Finset.ext_iff.mp hu a
  have hss : ∀ a,a∈s ↔ a∈t := fun a => by simpa using Finset.ext_iff.mp hs a
  ext a
  simp only [List.mem_toFinset,mem_expand,huu,hss]

theorem search_ext_universe (r : α → α → Bool) {u v : List α}
    (hu : u.toFinset=v.toFinset) (a : α) (n : ℕ) :
    (search r u a n).toFinset=(search r v a n).toFinset := by
  induction n with
  | zero => rfl
  | succ n ih => exact expand_ext_universe r hu ih

theorem search_add_stable (r : α → α → Bool) {u : List α} {a : α} (ha : a∈u) (k : ℕ) :
    (search r u a (u.length+k)).toFinset=(component r u a).toFinset := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (expand r u (search r u a (u.length+k))).toFinset=(component r u a).toFinset
    rw [expand_ext r u ih]
    exact search_stable r ha

theorem component_ext_universe (r : α → α → Bool) {u v : List α}
    (hu : u.toFinset=v.toFinset) {a : α} (ha : a∈u) :
    (component r u a).toFinset=(component r v a).toFinset := by
  have hv : a∈v := by
    apply List.mem_toFinset.mp
    rw [←hu]
    exact List.mem_toFinset.mpr ha
  rw [←search_add_stable r ha v.length,←search_add_stable r hv u.length,Nat.add_comm v.length]
  exact search_ext_universe r hu a _
end FiniteAlgebraicEnvelopes.Effect.Graph

namespace FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform
open FiniteAlgebraicEnvelopes.Effect
variable {P H B T : Type*} [Primcodable P] [Primcodable H] [Primcodable B] [Primcodable T]
  [Fintype B] [Fintype T] [DecidableEq H] [DecidableEq B] [DecidableEq T]

omit [Primcodable H] [Primcodable B] [Primcodable T] in
theorem universeList_ext_support {u v : List H} (h : u.toFinset=v.toFinset) (a : Sector H B T) :
    (universeList u a).toFinset=(universeList v a).toFinset := by
  have hh : ∀ q,q∈u ↔ q∈v := fun q => by simpa using Finset.ext_iff.mp h q
  ext b; simp only [List.mem_toFinset,mem_universeList,hh]

omit [Primcodable P] [Primcodable H] [Primcodable B] [Primcodable T] in
theorem componentList_ext_support (table : P → Table H B T) {u v : P → List H} (p : P)
    (h : (u p).toFinset=(v p).toFinset) (a : Sector H B T) (ha : a.head∈u p) :
    (componentList table u (p,a)).toFinset=(componentList table v (p,a)).toFinset := by
  apply Graph.component_ext_universe _ (universeList_ext_support h a)
  exact mem_universeList _ a a |>.mpr ⟨ha,rfl⟩

variable [LinearOrder (Sector H B T)]
noncomputable def representative (table : P → Table H B T) (support : P → List H)
    (entry success : Sector H B T → Bool) (x : P × Sector H B T) : Sector H B T :=
  (priorityList entry success (componentList table support x)).min?.getD x.2

theorem primrec_representative (table : P → Table H B T) {support : P → List H}
    {entry success : Sector H B T → Bool}
    (hb : Primrec (fun x : P × H => (table x.1).boundary x.2))
    (hc : Primrec (fun x : P × H × B × T => (table x.1).cell x.2.1 x.2.2.1 x.2.2.2))
    (hd : Primrec (fun x : P × H => decide ((table x.1).direction x.2 = .right)))
    (hs : Primrec support) (hp : Primrec entry) (hq : Primrec success)
    (hle : PrimrecRel (fun a b : Sector H B T => a ≤ b)) :
    Primrec (representative table support entry success) :=
  Primrec.option_getD.comp ((primrec_listMin hle).comp
    ((primrec_priorityList hp hq).comp (primrec_componentList table hb hc hd hs))) Primrec.snd

end FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform

namespace FiniteAlgebraicEnvelopes.Compiler
open HeadCodec FiniteAlgebraicEnvelopes.Effect
open scoped HeadCodec

namespace Control.Uniform
variable {S Γ Q : Type*} [Fintype S] [Fintype Γ] [Primcodable Q]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] in
theorem primrec_entry (blank : Γ) : PrimrecPred (Entry (S := S) (Q := Q) blank) :=
  (Primrec.eq.comp Scan.Sector.primrec_head (Primrec.const Head.initial)).and
    (Primrec.eq.comp (Primrec.list_head?.comp Scan.Sector.primrec_right)
      (Primrec.const (some (Validator.cell blank .cutD))))

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] in
theorem primrec_success : PrimrecPred (Success (S := S) (Γ := Γ) (Q := Q)) :=
  (Primrec.eq.comp Scan.Sector.primrec_head (Primrec.const (Head.machine .ok))).and
    ((Primrec.eq.comp Scan.Sector.primrec_right (Primrec.const [])).and
      (Primrec.eq.comp Scan.Sector.primrec_rb (Primrec.const true)))
end Control.Uniform

namespace Surface.Uniform
variable {P S Γ Q : Type*} [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable P]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
variable (blank : Γ) (rep : P × Control.Sector S Γ Q → Control.Sector S Γ Q)

def internalPreprocess (x : P × Control.Sector S Γ Q) : List (Sector S Γ (Control.Head S Q)) :=
  let w := rep x
  if Control.Entry blank w then
    pendingPreprocess blank ⟨w.left,.pending,w.right,w.leftBoundary,w.rightBoundary⟩
  else if Control.Success w then
    [cleanupPreprocess blank ⟨w.left,.cleanup,w.right,w.leftBoundary,w.rightBoundary⟩]
  else [Scan.mapHead Head.internal w]

def preprocess (x : P × Sector S Γ (Control.Head S Q)) : List (Sector S Γ (Control.Head S Q)) :=
  match x.2.head with
  | .raw => [rawNormal blank x.2]
  | .pending => pendingPreprocess blank x.2
  | .cleanup => [cleanupPreprocess blank x.2]
  | .internal q => internalPreprocess blank rep
      (x.1,⟨x.2.left,q,x.2.right,x.2.leftBoundary,x.2.rightBoundary⟩)

theorem primrec_internalPreprocess (hrep : Primrec rep) : Primrec (internalPreprocess blank rep) := by
  have hp := primrec_pendingPreprocess (S := S) (H := Control.Head S Q) blank
  have hc := primrec_cleanupPreprocess (S := S) (H := Control.Head S Q) blank
  have hl : Primrec (fun w : Control.Sector S Γ Q =>
      pendingPreprocess blank (⟨w.left,.pending,w.right,w.leftBoundary,w.rightBoundary⟩ : Sector S Γ (Control.Head S Q))) :=
    hp.comp (Scan.Sector.primrec_mk Scan.Sector.primrec_left (Primrec.const Head.pending)
      Scan.Sector.primrec_right Scan.Sector.primrec_lb Scan.Sector.primrec_rb)
  have hr : Primrec (fun w : Control.Sector S Γ Q =>
      cleanupPreprocess blank (⟨w.left,.cleanup,w.right,w.leftBoundary,w.rightBoundary⟩ : Sector S Γ (Control.Head S Q))) :=
    hc.comp (Scan.Sector.primrec_mk Scan.Sector.primrec_left (Primrec.const Head.cleanup)
      Scan.Sector.primrec_right Scan.Sector.primrec_lb Scan.Sector.primrec_rb)
  exact (Primrec.ite (Control.Uniform.primrec_entry blank) hl
    (Primrec.ite Control.Uniform.primrec_success (Primrec.list_cons.comp hr (Primrec.const []))
      (Primrec.list_cons.comp (Scan.primrec_mapHead HeadCodec.primrec_internal)
        (Primrec.const [])))).comp hrep

theorem primrec_preprocess (hrep : Primrec rep) : Primrec (preprocess blank rep) := by
  let inside : Head (Control.Head S Q) → Control.Head S Q
    | .internal q => q
    | _ => .initial
  have hin : Primrec inside :=
    ((primrec_sumElim (Primrec.const Control.Head.initial) Primrec.id).comp primrec_surfaceCode).of_eq
      fun q => by cases q <;> rfl
  have hv : Primrec (fun x : P × Sector S Γ (Control.Head S Q) =>
      (⟨x.2.left,inside x.2.head,x.2.right,x.2.leftBoundary,x.2.rightBoundary⟩ : Control.Sector S Γ Q)) :=
    (Scan.Sector.primrec_mk Scan.Sector.primrec_left
        (hin.comp Scan.Sector.primrec_head) Scan.Sector.primrec_right
          Scan.Sector.primrec_lb Scan.Sector.primrec_rb).comp (Primrec.snd (α :=P))
  have hi : Primrec (fun x : P × Sector S Γ (Control.Head S Q) =>
      internalPreprocess blank rep
        (x.1,⟨x.2.left,inside x.2.head,x.2.right,x.2.leftBoundary,x.2.rightBoundary⟩)) :=
    (primrec_internalPreprocess blank rep hrep).comp (Primrec.fst.pair hv)
  have hg (q : Head (Control.Head S Q)) :
      PrimrecPred (fun x : P × Sector S Γ (Control.Head S Q) => x.2.head = q) :=
    Primrec.eq.comp (Scan.Sector.primrec_head.comp Primrec.snd) (Primrec.const q)
  exact (Primrec.ite (hg .raw)
      (Primrec.list_cons.comp ((primrec_rawNormal blank).comp Primrec.snd) (Primrec.const []))
      (Primrec.ite (hg .pending) ((primrec_pendingPreprocess blank).comp Primrec.snd)
        (Primrec.ite (hg .cleanup)
          (Primrec.list_cons.comp ((primrec_cleanupPreprocess blank).comp Primrec.snd) (Primrec.const [])) hi))).of_eq
    fun x => by rcases x with ⟨p,l,q,r,lb,rb⟩; cases q <;> simp [preprocess,inside]
end Surface.Uniform

namespace Path.Uniform
variable {P C H : Type*} [Primcodable P] [Primcodable C] [Primcodable H]
  [DecidableEq C] [DecidableEq H]

theorem primrec_prepareChunk_family {norm : P × Sector C H → List (Sector C H)}
    (hn : Primrec norm) : Primrec (fun x : P × List (Letter C H) =>
      prepareChunk (fun v => norm (x.1,v)) x.2) := by
  exact (Primrec.option_casesOn (primrec_decode.comp Primrec.snd)
    (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
    (Primrec.list_map (hn.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))
      (primrec_encode.comp Primrec.snd).to₂).to₂).of_eq
        fun x => by cases h : decode x.2 <;> simp [prepareChunk,h]

theorem primrec_prepareChunks_family {norm : P × Sector C H → List (Sector C H)}
    (hn : Primrec norm) : Primrec (fun x : P × List (List (Letter C H)) =>
      prepareChunks (fun v => norm (x.1,v)) x.2) :=
  Primrec.list_flatMap Primrec.snd ((primrec_prepareChunk_family hn).comp
    ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂

theorem primrec_prepare_family {norm : P × Sector C H → List (Sector C H)}
    (hn : Primrec norm) : Primrec (fun x : P × List (Letter C H) =>
      prepare (fun v => norm (x.1,v)) x.2) :=
  (primrec_prepareChunks_family hn).comp (Primrec.fst.pair (primrec_cuts.comp Primrec.snd))
end Path.Uniform

namespace Word.Uniform
variable {P S Γ Q : Type*} [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable P]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
variable (blank : Γ) (rep : P × Control.Sector S Γ Q → Control.Sector S Γ Q)

def sectorPreprocess (x : P × Sector S Γ Q) : List (Sector S Γ Q) :=
  (Surface.Uniform.preprocess blank rep (x.1,Scan.unliteral x.2)).map (Scan.literal id)

def preprocess (x : P × List (Letter S Γ Q)) : List (List (Letter S Γ Q)) :=
  Path.prepare (fun v => sectorPreprocess blank rep (x.1,v)) x.2

theorem primrec_sectorPreprocess (hrep : Primrec rep) : Primrec (sectorPreprocess blank rep) :=
  Primrec.list_map ((Surface.Uniform.primrec_preprocess blank rep hrep).comp
    (Primrec.fst.pair (Scan.primrec_unliteral.comp Primrec.snd)))
    ((Scan.primrec_literal Primrec.id).comp Primrec.snd).to₂

theorem primrec_preprocess (hrep : Primrec rep) : Primrec (preprocess blank rep) :=
  Path.Uniform.primrec_prepare_family (primrec_sectorPreprocess blank rep hrep)

end Word.Uniform
end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.Effect
variable {P α β : Type*} [Primcodable P] [Primcodable α] [Primcodable β]

omit [Primcodable P] [Primcodable α] [Primcodable β] in
theorem traverse_map_parameter (f : P × α → Part β) (p : P) (l : List α) :
    traverse f (l.map (p,·))=traverse (fun a => f (p,a)) l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons,traverse,ih]

theorem partrec_traverse_family {f : P × α → Part β} (hf : Partrec f) :
    Partrec (fun x : P × List α => traverse (fun a => f (x.1,a)) x.2) := by
  have hp : Primrec (fun x : P × List α => x.2.map (x.1,·)) :=
    Primrec.list_map Primrec.snd ((Primrec.fst.comp Primrec.fst).pair Primrec.snd).to₂
  exact ((partrec_traverse hf).comp hp.to_comp).of_eq fun x => traverse_map_parameter f x.1 x.2
end FiniteAlgebraicEnvelopes.Effect

namespace FiniteAlgebraicEnvelopes.Compiler.RawRuns.Uniform
variable {P C S : Type*} [Primcodable P] [Primcodable C] [Primcodable S]

theorem partrec_action {f : P × List S → Part (List S)} (hf : Partrec f) :
    Partrec (fun x : P × Action C S => Action.partial (fun w => f (x.1,w)) x.2) := by
  have hh : Partrec₂ (fun (x : P × Action C S) (b : List S ⊕ List S) =>
      b.elim (fun w => Part.some (Sum.inr w : Item C S))
        (fun w => (f (x.1,w)).map (Sum.inr (α := C)))) := by
    exact (Partrec.sumCasesOn_right Computable.snd
      (Computable.sumInr.comp Computable.snd).to₂
      (((hf.comp ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair Computable.snd)).map
        (Computable.sumInr.comp Computable.snd).to₂).to₂)).to₂
  exact (Partrec.sumCasesOn_right (Action.primrec_code.to_comp.comp Computable.snd)
    (Computable.sumInl.comp Computable.snd).to₂ hh).of_eq fun x => by cases x.2 <;> rfl

theorem partrec_execute {f : P × List S → Part (List S)} (hf : Partrec f) :
    Partrec (fun x : P × List (Action C S) => execute (fun w => f (x.1,w)) x.2) := by
  apply (Effect.partrec_traverse_family (partrec_action (C := C) hf)).of_eq
  intro x
  induction x.2 with
  | nil => rfl
  | cons a l ih => simp only [Effect.traverse,execute,ih]

theorem partrec_partialSource {f : P × List S → Part (List S)} (hf : Partrec f) :
    Partrec (fun x : P × List (Item C S) => partialSource (fun w => f (x.1,w)) x.2) :=
  (partrec_execute hf).comp (Computable.fst.pair (primrec_plan.to_comp.comp Computable.snd))
end FiniteAlgebraicEnvelopes.Compiler.RawRuns.Uniform

namespace FiniteAlgebraicEnvelopes.Compiler
open HeadCodec FiniteAlgebraicEnvelopes.Effect
open scoped HeadCodec

namespace Word.Uniform
variable {P S Γ Q : Type*} [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable P] [Primcodable S]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
variable (blank : Γ) (rep : P × Control.Sector S Γ Q → Control.Sector S Γ Q)

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] in
theorem primrec_raw : Primrec (raw (S := S) (Q := Q) blank) := by
  have hp : Primrec (fun w : List S => (⟨[],Surface.Head.raw,
      w.map (Validator.cell blank ∘ Base.anchor),true,true⟩ : Surface.Sector S Γ (Control.Head S Q))) :=
    Scan.Sector.primrec_mk (Primrec.const []) (Primrec.const Surface.Head.raw)
      (Primrec.list_map Primrec.id ((Primrec.dom_finite _).comp Primrec.snd).to₂)
      (Primrec.const true) (Primrec.const true)
  exact Path.Uniform.primrec_encode.comp ((Scan.primrec_literal Primrec.id).comp hp)

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] in
theorem primrec_rawLetters : Primrec (rawLetters (S := S) (Γ := Γ) (Q := Q)) := by
  let f : Base S × Tag S Γ → Option S := fun c => match c.1 with | .anchor s => some s | _ => none
  have hp : Primrec (fun a : Letter S Γ Q => match a with
      | .right (.anchor s,_) => some s | _ => none) := by
    exact (Primrec.option_bind Path.Uniform.primrec_right?
      ((Primrec.dom_finite f).comp Primrec.snd).to₂).of_eq fun a => by
        cases a <;> simp only [Option.bind_none, Option.bind_some]
        case right c => cases c with | mk b t => cases b <;> rfl
  exact Primrec.listFilterMap Primrec.id (hp.comp Primrec.snd).to₂

theorem primrec_readRaw : Primrec (readRaw (S := S) (Q := Q) blank) :=
  Primrec.ite (Primrec.eq.comp ((primrec_raw blank).comp primrec_rawLetters) Primrec.id)
    (Primrec.option_some.comp primrec_rawLetters) (Primrec.const none)

theorem primrec_classify : Primrec (classify (S := S) (Q := Q) blank) := by
  exact (Primrec.option_casesOn (primrec_readRaw blank) Primrec.sumInl
    (Primrec.sumInr.comp Primrec.snd).to₂).of_eq fun w => by
      cases h : readRaw blank w <;> simp [classify,h]

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] in
theorem primrec_realize : Primrec (realize (S := S) (Q := Q) blank) := by
  exact (Primrec.sumCasesOn Primrec.id Primrec.snd.to₂
    ((primrec_raw blank).comp Primrec.snd).to₂).of_eq fun w => by cases w <;> rfl

def partialNormal (f : P × List S → Part (List S))
    (x : P × List (Letter S Γ Q)) : Part (List (Letter S Γ Q)) :=
  if Path.shape x.2 = .zero then Part.some [.zero] else
    (RawRuns.partialSource (fun w => f (x.1,w)) ((preprocess blank rep x).map (classify blank))).map
      (List.flatMap (realize blank))

theorem partrec_partialNormal (hrep : Primrec rep)
    {f : P × List S → Part (List S)} (hf : Partrec f) :
    Partrec (partialNormal blank rep f) := by
  have hp : Primrec (fun x : P × List (Letter S Γ Q) =>
      (preprocess blank rep x).map (classify blank)) :=
    Primrec.list_map (primrec_preprocess blank rep hrep) ((primrec_classify blank).comp Primrec.snd).to₂
  have hr : Primrec (fun w : List (Item S Γ Q) => w.flatMap (realize blank)) :=
    Primrec.list_flatMap Primrec.id ((primrec_realize blank).comp Primrec.snd).to₂
  have hb : Partrec (fun x : P × List (Letter S Γ Q) =>
      (RawRuns.partialSource (fun w => f (x.1,w)) ((preprocess blank rep x).map (classify blank))).map
        (List.flatMap (realize blank))) :=
    ((RawRuns.Uniform.partrec_partialSource hf).comp (Computable.fst.pair hp.to_comp)).map
      (hr.to_comp.comp Computable.snd).to₂
  have ho : Primrec (fun x : P × List (Letter S Γ Q) =>
      if Path.shape x.2 = .zero then none else some x) :=
    Primrec.ite (Primrec.eq.comp (Path.Uniform.primrec_shape.comp Primrec.snd) (Primrec.const Path.Shape.zero))
      (Primrec.const none) Primrec.option_some
  exact (Partrec.optionCasesOn_right ho.to_comp (Computable.const [Path.Letter.zero])
    (hb.comp Computable.snd).to₂).of_eq fun x => by
      by_cases h : Path.shape x.2 = .zero <;> simp [h,partialNormal]

end Word.Uniform
end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.Effect
variable {α β : Type*}

theorem priorityList_map (i : α → β) (p q : α → Bool) (p' q' : β → Bool)
    (hp : ∀ a,p' (i a)=p a) (hq : ∀ a,q' (i a)=q a) (s : List α) :
    priorityList p' q' (s.map i)=(priorityList p q s).map i := by
  have he (f : α → Bool) (g : β → Bool) (h : ∀ a,g (i a)=f a) :
      (s.map i).filter g=(s.filter f).map i := by
    rw [List.filter_map]; simp only [Function.comp_def,h]
  simp only [priorityList,he p p' hp,he q q' hq,List.isEmpty_map]
  split <;> first | rfl | (split <;> rfl)

theorem priorityList_ext [Primcodable α] [DecidableEq α] (p q : α → Bool) {s t : List α}
    (he : s.toFinset=t.toFinset) :
    (priorityList p q s).toFinset=(priorityList p q t).toFinset := by
  simp only [priorityList_toFinset,he]

variable [LinearOrder α] [LinearOrder β]

theorem minList_map (i : α → β) (hi : Monotone i) (s : List α) :
    (s.map i).min?=s.min?.map i := by
  cases h : s.min? with
  | none =>
    have hs := List.min?_eq_none_iff.mp h
    subst s; rfl
  | some a =>
    simp only [Option.map_some]
    obtain ⟨ha,hm⟩ := List.min?_eq_some_iff.mp h
    apply List.min?_eq_some_iff.mpr
    refine ⟨List.mem_map.mpr ⟨a,ha,rfl⟩,?_⟩
    rintro b hb
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
    exact hi (hm c hc)

theorem minList_ext [DecidableEq α] {s t : List α} (he : s.toFinset=t.toFinset) :
    s.min?=t.min? := by
  have hm : ∀ a,a∈s ↔ a∈t := fun a => by simpa using Finset.ext_iff.mp he a
  apply Option.ext
  intro a
  simp only [List.min?_eq_some_iff,hm]

end FiniteAlgebraicEnvelopes.Effect

namespace FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform
open FiniteAlgebraicEnvelopes.Effect
variable {H H' B T : Type*} [Primcodable H] [Primcodable H'] [Primcodable B] [Primcodable T]
  [Fintype B] [Fintype T] [DecidableEq H] [DecidableEq H'] [DecidableEq B] [DecidableEq T]
  [LinearOrder (Sector H B T)] [LinearOrder (Sector H' B T)]

variable (i : H → H') (hi : Function.Injective i)
  (t : Table H B T) (u : Table H' B T)
  (hd : ∀ q,u.direction (i q)=t.direction q)
  (hc : ∀ q b a,u.cell (i q) b a=(t.cell q b a).map (mapInstruction i))
  (hb : ∀ q,u.boundary (i q)=(t.boundary q).map i)
  (ho : Monotone (mapHead (B := B) (T := T) i))
  (entry success : Sector H B T → Bool) (entry' success' : Sector H' B T → Bool)
  (he : ∀ v,entry' (mapHead i v)=entry v) (hs : ∀ v,success' (mapHead i v)=success v)

omit [Primcodable H] [Primcodable H'] [Primcodable B] [Primcodable T] in
include hi hd hc hb ho he hs in
theorem representative_map (heads : List H) (v : Sector H B T) :
    representative (fun _ : Unit => u) (fun _ => heads.map i) entry' success' ((),mapHead i v)=
      mapHead i (representative (fun _ : Unit => t) (fun _ => heads) entry success ((),v)) := by
  unfold representative
  rw [componentList_map i hi t u hd hc hb heads v,priorityList_map _ _ _ _ _ he hs,minList_map _ ho]
  cases (priorityList entry success (componentList (fun _ : Unit => t) (fun _ => heads) ((),v))).min? <;> rfl

variable {P : Type*} [Primcodable P]
omit [Primcodable P] in
theorem representative_ext_support (table : P → Table H B T) {heads heads' : P → List H}
    (p : P) (he : (heads p).toFinset=(heads' p).toFinset)
    (entry success : Sector H B T → Bool) (v : Sector H B T) (hv : v.head∈heads p) :
    representative table heads entry success (p,v)=representative table heads' entry success (p,v) := by
  unfold representative
  rw [minList_ext (priorityList_ext _ _ (componentList_ext_support table p he v hv))]

variable [Fintype H]
omit [Primcodable H] [Primcodable B] [Primcodable T] in
theorem representative_finite (t : Table H B T) (E F : Sector H B T → Prop)
    [DecidablePred E] [DecidablePred F] (v : Sector H B T) :
    representative (fun _ : Unit => t) (fun _ => finiteList H)
      (fun w => decide (E w)) (fun w => decide (F w)) ((),v)=Scan.representative t E F v :=
  (Scan.representative_list t E F v).symm

omit [Primcodable H] in
include hi hd hc hb ho he hs in
theorem representative_finite_map (heads : List H')
    (hh : heads.toFinset=((finiteList H).map i).toFinset) (v : Sector H B T) :
    representative (fun _ : Unit => u) (fun _ => heads) entry' success' ((),mapHead i v)=
      mapHead i (Scan.representative t (fun w => entry w=true) (fun w => success w=true) v) := by
  have hv : (mapHead i v).head∈heads := by
    apply List.mem_toFinset.mp
    rw [hh]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨v.head,mem_finiteList _,rfl⟩)
  rw [representative_ext_support (heads' := fun _ : Unit => (finiteList H).map i) (fun _ : Unit => u) () hh entry' success' _ hv,
    representative_map i hi t u hd hc hb ho entry success entry' success' he hs]
  congr 1
  simpa only [Bool.decide_coe] using
    representative_finite t (fun w => entry w=true) (fun w => success w=true) v

end FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform

namespace FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

section
open Compiler Compiler.Simulator Compiler.HeadCodec ParameterMachine
open scoped Compiler.HeadCodec
variable {S Γ Q : Type*}

variable (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ] (p : S)
def codedMachine (n : ℕ) : Machine (Control Q) (Bool×Γ) where
  initial := .inl 0
  transition q a := (transition A M p n q a).map (fun c => ⟨c.1,c.2.1,c.2.2⟩)

theorem coded_initial (n : ℕ) :
    (codedMachine A M p n).initial=encode n (ParameterMachine.machine A M p n).initial := rfl

theorem coded_transition (n : ℕ) (q : State Q n) (a : Bool×Γ) :
    (codedMachine A M p n).transition (encode n q) a=
      ((ParameterMachine.machine A M p n).transition q a).map (commandMap (encode n)) := by
  simp only [codedMachine,transition_encode,Option.map_map]
  rfl

variable [Fintype Q] [Fintype Γ] [Primcodable Q] [Primcodable Γ]
theorem primrec_codedTransition : Primrec (fun x : ℕ × Control Q × (Bool×Γ) =>
    (codedMachine A M p x.1).transition x.2.1 x.2.2) := by
  have ht := (primrec_transition A M p).comp
    ((Primrec.fst.pair (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd))
  exact Primrec.option_map ht
    (primrec_commandMk (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂

omit [Primcodable Q] in
theorem mem_support_iff (n : ℕ) (q : Control Q) :
    q∈support n ↔ ∃ a : State Q n,encode n a=q := by
  constructor
  · intro h
    cases q with
    | inr q => exact ⟨.run q,rfl⟩
    | inl k =>
      have hk : k<n+5 := by simpa [support] using h
      by_cases h0 : k=0
      · subst k; exact ⟨.start,rfl⟩
      by_cases h1 : k=1
      · subst k; exact ⟨.scan,rfl⟩
      by_cases h2 : k=2
      · subst k; exact ⟨.rewind,rfl⟩
      refine ⟨.emit ⟨k-3,by omega⟩,?_⟩
      simp only [encode,Sum.inl.injEq]
      omega
  · rintro ⟨a,rfl⟩
    exact mem_support n a

variable {T : Type*} [Fintype T]
noncomputable def heads (n : ℕ) : List (Compiler.Control.Head T (Control Q)) :=
  controlSupport (support n)

theorem primrec_heads : Primrec (heads (T := T) (Q := Q)) :=
  primrec_controlSupport.comp primrec_support

omit [Primcodable Q] in
theorem mem_heads_iff (n : ℕ) (h : Compiler.Control.Head T (Control Q)) :
    h∈heads n ↔ ∃ a : Compiler.Control.Head T (State Q n),controlMap (encode n) a=h := by
  constructor
  · intro hh
    cases h with
    | initial => exact ⟨.initial,rfl⟩
    | left => exact ⟨.left,rfl⟩
    | right => exact ⟨.right,rfl⟩
    | workspace => exact ⟨.workspace,rfl⟩
    | suffix => exact ⟨.suffix,rfl⟩
    | machine h =>
      cases h with
      | start => exact ⟨.machine .start,rfl⟩
      | rewind r => exact ⟨.machine (.rewind r),rfl⟩
      | scan r => exact ⟨.machine (.scan r),rfl⟩
      | finish => exact ⟨.machine .finish,rfl⟩
      | ok => exact ⟨.machine .ok,rfl⟩
      | run q =>
        obtain ⟨a,rfl⟩ := (mem_support_iff n q).mp ((mem_controlSupport _ _).mp hh)
        exact ⟨.machine (.run a),rfl⟩
      | left q =>
        obtain ⟨a,rfl⟩ := (mem_support_iff n q).mp ((mem_controlSupport _ _).mp hh)
        exact ⟨.machine (.left a),rfl⟩
  · rintro ⟨a,rfl⟩
    cases a <;> simp only [heads,mem_controlSupport,controlMap]
    case machine a => cases a <;> simp [stateMap,mem_support]

omit [Primcodable Q] in
theorem heads_finset [DecidableEq T] [DecidableEq Q] (n : ℕ) :
    (heads (T := T) (Q := Q) n).toFinset=
      ((Scan.finiteList (Compiler.Control.Head T (State Q n))).map (controlMap (encode n))).toFinset := by
  classical
  ext h
  simp only [List.mem_toFinset,mem_heads_iff,List.mem_map,Scan.mem_finiteList,true_and]

end

open Compiler Compiler.Simulator Compiler.HeadCodec ParameterMachine
open scoped Compiler.HeadCodec
variable {S T Γ Q : Type*} [Fintype T] [Fintype Γ] [Fintype Q]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q]
variable (A : Alphabet S Γ) (M : Machine Q Γ) (p : S) (B : Alphabet T (Bool×Γ))

noncomputable def codedRepresentative : ℕ × Compiler.Control.Sector T (Bool×Γ) (Control Q) →
    Compiler.Control.Sector T (Bool×Γ) (Control Q) :=
  letI := Effect.codeOrder (Compiler.Control.Sector T (Bool×Γ) (Control Q))
  Scan.Uniform.representative (fun n => Compiler.Control.table B (codedMachine A M p n)) heads
    (fun v => decide (Compiler.Control.Entry B.blank v))
    (fun v => decide (Compiler.Control.Success v))

theorem primrec_codedRepresentative : Primrec (codedRepresentative A M p B) := by
  let := Effect.codeOrder (Compiler.Control.Sector T (Bool×Γ) (Control Q))
  apply Scan.Uniform.primrec_representative
  · exact primrec_controlBoundary B (codedMachine A M p) (Primrec.const _)
  · exact primrec_controlCell B (codedMachine A M p) (Primrec.const _) (primrec_codedTransition A M p)
  · exact primrec_controlDirection B (codedMachine A M p)
  · exact primrec_heads
  · exact (Compiler.Control.Uniform.primrec_entry B.blank).decide
  · exact (Compiler.Control.Uniform.primrec_success).decide
  · exact Effect.primrec_codeOrder _

@[instance_reducible]
noncomputable def finiteOrder (n : ℕ) : LinearOrder (Compiler.Control.Sector T (Bool×Γ) (State Q n)) :=
  letI := Effect.codeOrder (Compiler.Control.Sector T (Bool×Γ) (Control Q))
  LinearOrder.lift' (Scan.mapHead (controlMap (encode n)))
    (Scan.Uniform.mapHead_injective _ (controlMap_injective (encode_injective n)))

omit [Primcodable Γ] in
theorem codedRepresentative_map (n : ℕ) (v : Compiler.Control.Sector T (Bool×Γ) (State Q n)) :
    letI := finiteOrder (T := T) (Γ := Γ) (Q := Q) n
    codedRepresentative A M p B (n,Scan.mapHead (controlMap (encode n)) v)=
      Scan.mapHead (controlMap (encode n)) (Compiler.Control.representative B (machine A M p n) v) := by
  let : Primcodable (State Q n) := Effect.finitePrimcodable _
  let := Effect.codeOrder (Compiler.Control.Sector T (Bool×Γ) (Control Q))
  let := finiteOrder (T := T) (Γ := Γ) (Q := Q) n
  have h := Scan.Uniform.representative_finite_map
    (controlMap (S := T) (encode n)) (controlMap_injective (encode_injective n))
    (Compiler.Control.table B (machine A M p n)) (Compiler.Control.table B (codedMachine A M p n))
    (Compiler.Control.table_direction_map B (machine A M p n) (codedMachine A M p n) (encode n))
    (Compiler.Control.table_cell_map B (machine A M p n) (codedMachine A M p n) (encode n)
      (coded_initial A M p n) (coded_transition A M p n))
    (Compiler.Control.table_boundary_map B (machine A M p n) (codedMachine A M p n) (encode n))
    (show Monotone (Scan.mapHead (B := Base T) (T := Tag T (Bool×Γ)) (controlMap (encode n))) from
      fun _ _ h => h)
    (fun w => decide (Compiler.Control.Entry B.blank w)) (fun w => decide (Compiler.Control.Success w))
    (fun w => decide (Compiler.Control.Entry B.blank w)) (fun w => decide (Compiler.Control.Success w))
    (fun w => by simp only [Compiler.Control.entry_map])
    (fun w => by simp only [Compiler.Control.success_map])
    (heads n) (heads_finset n) v
  simpa only [codedRepresentative, Compiler.Control.representative,
    Scan.Uniform.representative, Scan.Uniform.componentList,decide_eq_true_eq] using h

end FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

namespace FiniteAlgebraicEnvelopes.Compiler.Surface
variable {S Γ H H' : Type*}

def headMap (i : H → H') : Head H → Head H'
  | .raw => .raw | .pending => .pending | .cleanup => .cleanup | .internal q => .internal (i q)

theorem headMap_injective {i : H → H'} (hi : Function.Injective i) : Function.Injective (headMap i) := by
  intro a b h; cases a <;> cases b <;> simp_all [headMap]
  exact hi h

variable (i : H → H') (blank : Γ) [DecidableEq S] [DecidableEq Γ]

theorem rawSweep_map (l r : Cells S Γ) (lb rb : Bool) :
    rawSweep (H := H') blank l r lb rb=Scan.mapHead (headMap i) (rawSweep (H := H) blank l r lb rb) := by
  induction l generalizing r with
  | nil => rfl
  | cons c l ih =>
    rcases c with ⟨b,t⟩
    cases b <;> simp only [rawSweep]
    case anchor s => split <;> first | exact ih _ | rfl
    all_goals rfl

theorem rawNormal_map (v : Sector S Γ H) :
    rawNormal blank (Scan.mapHead (headMap i) v)=Scan.mapHead (headMap i) (rawNormal blank v) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> first | exact rawSweep_map i blank _ _ _ _ | rfl

theorem quotaNormal_map (v : Sector S Γ H) :
    quotaNormal blank (Scan.mapHead (headMap i) v)=Scan.mapHead (headMap i) (quotaNormal blank v) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> try rfl
  cases r <;> simp only [quotaNormal,Scan.mapHead,headMap]
  all_goals split <;> rfl

theorem unmerge_map (v : Sector S Γ H) :
    unmerge blank (Scan.mapHead (headMap i) v)=
      (unmerge blank v).map (Scan.mapHead (headMap i)) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases l <;> cases q <;> cases r <;> simp only [Scan.mapHead,headMap,unmerge,List.map_cons,List.map_nil]
  split
  · simp only [List.map_cons,List.map_nil]
    refine congrArg₂ (fun (a b : Sector S Γ H') => [a,b]) ?_ ?_
    · exact rawSweep_map (S := S) i blank _ _ _ _
    · exact rawSweep_map (S := S) i blank _ _ _ _
  · rfl

theorem pendingPreprocess_map (v : Sector S Γ H) :
    pendingPreprocess blank (Scan.mapHead (headMap i) v)=
      (pendingPreprocess blank v).map (Scan.mapHead (headMap i)) := by
  simp only [pendingPreprocess,quotaNormal_map,unmerge_map]

omit [DecidableEq S] [DecidableEq Γ] in
theorem ofCleanup_map (v : Cleanup.Sector S Γ) :
    (ofCleanup v : Sector S Γ H')=Scan.mapHead (headMap i) (ofCleanup v : Sector S Γ H) := by
  rcases v with ⟨l,q,r,lb,rb⟩; cases q <;> rfl

omit [DecidableEq S] [DecidableEq Γ] in
theorem cleanupNormal_map (v : Sector S Γ H) :
    cleanupNormal blank (Scan.mapHead (headMap i) v)=Scan.mapHead (headMap i) (cleanupNormal blank v) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> try rfl
  exact ofCleanup_map i _

theorem cleanupPreprocess_map (v : Sector S Γ H) :
    cleanupPreprocess blank (Scan.mapHead (headMap i) v)=Scan.mapHead (headMap i) (cleanupPreprocess blank v) := by
  simp only [cleanupPreprocess,cleanupNormal_map,rawNormal_map]
end FiniteAlgebraicEnvelopes.Compiler.Surface

namespace FiniteAlgebraicEnvelopes.Compiler.Surface.Uniform
open HeadCodec
open scoped HeadCodec
variable {P S Γ Q Q' : Type*} [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable Q'] [Primcodable P]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] [DecidableEq Q']
variable (i : Q → Q') (blank : Γ)
  (rep : P × Control.Sector S Γ Q → Control.Sector S Γ Q)
  (rep' : P × Control.Sector S Γ Q' → Control.Sector S Γ Q')
  (hr : ∀ p v,rep' (p,Scan.mapHead (controlMap i) v)=Scan.mapHead (controlMap i) (rep (p,v)))

omit [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable Q'] [Primcodable P] in
include hr in
theorem internalPreprocess_map (p : P) (v : Control.Sector S Γ Q) :
    internalPreprocess blank rep' (p,Scan.mapHead (controlMap i) v)=
      (internalPreprocess blank rep (p,v)).map (Scan.mapHead (Surface.headMap (controlMap i))) := by
  simp only [internalPreprocess,hr,Control.entry_map,Control.success_map]
  split
  · exact Surface.pendingPreprocess_map (controlMap i) blank
      (⟨(rep (p,v)).left,.pending,(rep (p,v)).right,(rep (p,v)).leftBoundary,(rep (p,v)).rightBoundary⟩ : Surface.Sector S Γ (Control.Head S Q))
  · split
    · simp only [List.map_cons,List.map_nil]
      congr 1
      exact Surface.cleanupPreprocess_map (controlMap i) blank
        (⟨(rep (p,v)).left,.cleanup,(rep (p,v)).right,(rep (p,v)).leftBoundary,(rep (p,v)).rightBoundary⟩ : Surface.Sector S Γ (Control.Head S Q))
    · rfl

omit [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable Q'] [Primcodable P] in
include hr in
theorem preprocess_map (p : P) (v : Surface.Sector S Γ (Control.Head S Q)) :
    preprocess blank rep' (p,Scan.mapHead (Surface.headMap (controlMap i)) v)=
      (preprocess blank rep (p,v)).map (Scan.mapHead (Surface.headMap (controlMap i))) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> simp only [preprocess,headMap,Scan.mapHead,List.map_cons,List.map_nil]
  case raw => congr 1; exact Surface.rawNormal_map (controlMap i) blank (⟨l,.raw,r,lb,rb⟩ : Surface.Sector S Γ (Control.Head S Q))
  case pending => exact Surface.pendingPreprocess_map (controlMap i) blank (⟨l,.pending,r,lb,rb⟩ : Surface.Sector S Γ (Control.Head S Q))
  case cleanup => congr 1; exact Surface.cleanupPreprocess_map (controlMap i) blank (⟨l,.cleanup,r,lb,rb⟩ : Surface.Sector S Γ (Control.Head S Q))
  case internal q => exact internalPreprocess_map i blank rep rep' hr p ⟨l,q,r,lb,rb⟩

end FiniteAlgebraicEnvelopes.Compiler.Surface.Uniform

namespace FiniteAlgebraicEnvelopes.Compiler.Path
variable {C H H' : Type*}

def mapLetter (i : H → H') : Letter C H → Letter C H'
  | .zero => .zero
  | .enter => .enter
  | .leave => .leave
  | .left c => .left c
  | .right c => .right c
  | .head q => .head (i q)

def mapSector (i : H → H') (v : Sector C H) : Sector C H' :=
  ⟨v.left,i v.head,v.right,v.leftBoundary,v.rightBoundary⟩

variable (i : H → H')
@[simp] theorem typeOf_mapLetter (a : Letter C H) : typeOf (mapLetter i a)=typeOf a := by
  cases a <;> rfl
@[simp] theorem shape_map (w : List (Letter C H)) : shape (w.map (mapLetter i))=shape w := by
  simp [shape,List.map_map,Function.comp_def]

theorem mapLetter_injective (hi : Function.Injective i) : Function.Injective (mapLetter (C := C) i) := by
  intro a b h
  cases a <;> cases b <;> simp_all [mapLetter]
  exact hi h

@[simp] theorem headed_map (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    (headed l q r lb rb).map (mapLetter i)=headed l (i q) r lb rb := by
  cases lb <;> cases rb <;> simp [headed,List.map_map,Function.comp_def,mapLetter]
@[simp] theorem encode_map (v : Sector C H) :
    encode (mapSector i v)=(encode v).map (mapLetter i) := (headed_map i _ _ _ _ _).symm

@[simp] theorem heads_map (w : List (Letter C H)) :
    heads (w.map (mapLetter i))=(heads w).map i := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp only [heads,List.map_cons,List.filterMap_cons,mapLetter] at * <;> simp_all
@[simp] theorem lefts_map (w : List (Letter C H)) : lefts (w.map (mapLetter i))=lefts w := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp only [lefts,List.map_cons,List.filterMap_cons,mapLetter] at * <;> simp_all
@[simp] theorem rights_map (w : List (Letter C H)) : rights (w.map (mapLetter i))=rights w := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp only [rights,List.map_cons,List.filterMap_cons,mapLetter] at * <;> simp_all
@[simp] theorem enter_mem_map (w : List (Letter C H)) :
    .enter ∈ w.map (mapLetter i) ↔ .enter ∈ w := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨a,ha,he⟩; cases a <;> simp [mapLetter] at he; exact ha
  · intro h; exact ⟨.enter,h,rfl⟩
@[simp] theorem leave_mem_map (w : List (Letter C H)) :
    .leave ∈ w.map (mapLetter i) ↔ .leave ∈ w := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨a,ha,he⟩; cases a <;> simp [mapLetter] at he; exact ha
  · intro h; exact ⟨.leave,h,rfl⟩

variable [DecidableEq C] [DecidableEq H] [DecidableEq H']
theorem decode_map (hi : Function.Injective i) (w : List (Letter C H)) :
    decode (w.map (mapLetter i))=(decode w).map (mapSector i) := by
  have he (v : Sector C H) : encode (mapSector i v)=w.map (mapLetter i) ↔ encode v=w := by
    rw [encode_map]
    exact List.map_injective_iff.mpr (mapLetter_injective i hi) |>.eq_iff
  unfold decode
  rw [heads_map]
  cases h : heads w with
  | nil => rfl
  | cons q qs =>
    cases qs with
    | cons q' qs => rfl
    | nil =>
      simp only [List.map_cons,List.map_nil,lefts_map,rights_map,enter_mem_map,leave_mem_map]
      let v : Sector C H := ⟨(lefts w).reverse,q,rights w,decide (.enter∈w),decide (.leave∈w)⟩
      change (if encode (mapSector i v) = w.map (mapLetter i) then some (mapSector i v) else none) = _
      simp only [he]
      split <;> rfl

omit [DecidableEq C] [DecidableEq H] [DecidableEq H'] in
theorem glue_map (w : List (Letter C H)) (ws : List (List (Letter C H))) :
    glue (w.map (mapLetter i)) (ws.map (List.map (mapLetter i)))=
      (glue w ws).map (List.map (mapLetter i)) := by
  cases ws <;> cases w <;> simp [glue]
omit [DecidableEq C] [DecidableEq H] [DecidableEq H'] in
@[simp] theorem cuts_map (w : List (Letter C H)) :
    cuts (w.map (mapLetter i))=(cuts w).map (List.map (mapLetter i)) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have hh := glue_map i [a] (cuts w)
    cases a <;> simp only [List.map_cons,List.map_nil,mapLetter,cuts,ih] at hh ⊢ <;> exact hh

variable (p : Sector C H → List (Sector C H)) (p' : Sector C H' → List (Sector C H'))
  (hp : ∀ v,p' (mapSector i v)=(p v).map (mapSector i))
include hp in
theorem prepareChunk_map (hi : Function.Injective i) (w : List (Letter C H)) :
    prepareChunk p' (w.map (mapLetter i))=(prepareChunk p w).map (List.map (mapLetter i)) := by
  unfold prepareChunk
  rw [decode_map i hi]
  cases h : decode w with
  | none => rfl
  | some v => simp only [Option.map_some,hp,List.map_map,Function.comp_def,encode_map]
include hp in
theorem prepare_map (hi : Function.Injective i) (w : List (Letter C H)) :
    prepare p' (w.map (mapLetter i))=(prepare p w).map (List.map (mapLetter i)) := by
  simp only [prepare,prepareChunks,cuts_map,List.flatMap_map,List.map_flatMap]
  congr 1
  funext a
  exact prepareChunk_map i p p' hp hi a

end FiniteAlgebraicEnvelopes.Compiler.Path

namespace FiniteAlgebraicEnvelopes.Compiler.RawRuns
variable {C D S : Type*} (i : C → D)

def Action.mapKeep : Action C S → Action D S
  | .keep c => .keep (i c)
  | .raw w => .raw w
  | .call w => .call w

theorem splitRun_map (w : List (Item C S)) :
    splitRun (w.map (Sum.map i id))=((splitRun w).1,(splitRun w).2.map (Sum.map i id)) := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp only [List.map_cons,Sum.map_inl,Sum.map_inr,id_eq,splitRun,ih]

theorem plan_map (w : List (Item C S)) :
    plan (w.map (Sum.map i id))=(plan w).map (Action.mapKeep i) := by
  cases w with
  | nil => simp only [List.map_nil,plan]
  | cons a w =>
    cases a with
    | inl c => simp only [List.map_cons,Sum.map_inl,plan,Action.mapKeep,plan_map w]
    | inr x =>
      rw [List.map_cons]
      simp only [Sum.map_inr,id_eq,plan,splitRun_map,List.map_cons,plan_map (splitRun w).2]
      cases (splitRun w).1 <;> rfl
termination_by w.length
decreasing_by all_goals have := splitRun_length w; simp_all only [List.length_cons]; omega

theorem Action.partial_map (f : List S → Part (List S)) (a : Action C S) :
    (a.mapKeep i).partial f=(a.partial f).map (Sum.map i id) := by
  cases a <;> simp only [Action.mapKeep,Action.partial,Part.map_some,Part.map_map,
    Function.comp_def,Sum.map_inl,Sum.map_inr,id_eq]

theorem execute_map (f : List S → Part (List S)) (p : List (Action C S)) :
    execute f (p.map (Action.mapKeep i))=(execute f p).map (List.map (Sum.map i id)) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [List.map_cons,execute,Action.partial_map,ih,Part.bind_map,Part.map_bind,Part.map_map]
    congr 1

theorem partialSource_map (f : List S → Part (List S)) (w : List (Item C S)) :
    partialSource f (w.map (Sum.map i id))=(partialSource f w).map (List.map (Sum.map i id)) := by
  simp only [partialSource,plan_map,execute_map]

end FiniteAlgebraicEnvelopes.Compiler.RawRuns

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
variable {H H' B T : Type*} (i : H → H')
theorem unliteral_map (v : Path.Sector (B×T) H) :
    unliteral (Path.mapSector i v)=mapHead i (unliteral v) := rfl
theorem literal_map (v : Sector H B T) :
    literal id (mapHead i v)=Path.mapSector i (literal id v) := rfl
end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Word
open HeadCodec
variable {S Γ Q Q' : Type*} (i : Q → Q') (blank : Γ)

def headMap : Surface.Head (Control.Head S Q) → Surface.Head (Control.Head S Q') :=
  Surface.headMap (controlMap i)
def letterMap : Letter S Γ Q → Letter S Γ Q' := Path.mapLetter (headMap i)

theorem headMap_injective (hi : Function.Injective i) : Function.Injective (headMap (S := S) i) :=
  Surface.headMap_injective (controlMap_injective hi)
theorem letterMap_injective (hi : Function.Injective i) :
    Function.Injective (letterMap (S := S) (Γ := Γ) i) :=
  Path.mapLetter_injective _ (headMap_injective i hi)

@[simp] theorem raw_map (w : List S) : (raw (Q := Q) blank w).map (letterMap i)=raw blank w := by
  simp only [raw,encode,letterMap,←Path.encode_map]
  rfl

@[simp] theorem rawLetters_map (w : List (Letter S Γ Q)) : rawLetters (w.map (letterMap i))=rawLetters w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases a with
    | right c =>
      rcases c with ⟨b,t⟩
      cases b <;> simp_all only [List.map_cons,rawLetters,List.filterMap_cons,letterMap,Path.mapLetter]
    | _ => simp_all only [List.map_cons,rawLetters,List.filterMap_cons,letterMap,Path.mapLetter]

variable [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] [DecidableEq Q']
theorem readRaw_map (hi : Function.Injective i) (w : List (Letter S Γ Q)) :
    readRaw blank (w.map (letterMap i))=readRaw blank w := by
  have he : raw blank (rawLetters w)=w.map (letterMap i) ↔ raw blank (rawLetters w)=w := by
    rw [←raw_map i blank]
    exact List.map_injective_iff.mpr (letterMap_injective i hi) |>.eq_iff
  simp only [readRaw,rawLetters_map,he]

theorem classify_map (hi : Function.Injective i) (w : List (Letter S Γ Q)) :
    classify blank (w.map (letterMap i))=Sum.map (List.map (letterMap i)) id (classify blank w) := by
  simp only [classify,readRaw_map i blank hi]
  cases readRaw blank w <;> rfl

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] [DecidableEq Q'] in
theorem realize_map (a : Item S Γ Q) :
    realize blank (Sum.map (List.map (letterMap i)) id a)=(realize blank a).map (letterMap i) := by
  cases a <;> simp only [Sum.map_inl,Sum.map_inr,realize,raw_map,id_eq]
end FiniteAlgebraicEnvelopes.Compiler.Word

namespace FiniteAlgebraicEnvelopes.Compiler.Word.Uniform
open HeadCodec
open scoped HeadCodec
variable {P S Γ Q Q' : Type*} [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable Q'] [Primcodable P]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] [DecidableEq Q']
variable (i : Q → Q') (blank : Γ)
  (rep : P × Control.Sector S Γ Q → Control.Sector S Γ Q)
  (rep' : P × Control.Sector S Γ Q' → Control.Sector S Γ Q')
  (hr : ∀ p v,rep' (p,Scan.mapHead (controlMap i) v)=Scan.mapHead (controlMap i) (rep (p,v)))

include hr in
omit [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable Q'] [Primcodable P] in
theorem sectorPreprocess_map (p : P) (v : Sector S Γ Q) :
    sectorPreprocess blank rep' (p,Path.mapSector (headMap i) v)=
      (sectorPreprocess blank rep (p,v)).map (Path.mapSector (headMap i)) := by
  simp only [sectorPreprocess,Scan.unliteral_map,headMap,
    Surface.Uniform.preprocess_map i blank rep rep' hr,List.map_map,Function.comp_def,Scan.literal_map]

include hr in
omit [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable Q'] [Primcodable P] in
theorem preprocess_map (hi : Function.Injective i) (p : P) (w : List (Letter S Γ Q)) :
    preprocess blank rep' (p,w.map (letterMap i))=
      (preprocess blank rep (p,w)).map (List.map (letterMap i)) :=
  Path.prepare_map (headMap i) _ _ (sectorPreprocess_map i blank rep rep' hr p)
    (headMap_injective i hi) w

include hr in
omit [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable Q'] [Primcodable P] in
theorem partialNormal_map (hi : Function.Injective i) (f : P × List S → Part (List S))
    (p : P) (w : List (Letter S Γ Q)) :
    partialNormal blank rep' f (p,w.map (letterMap i))=
      (partialNormal blank rep f (p,w)).map (List.map (letterMap i)) := by
  have hshape : Path.shape (w.map (letterMap i))=Path.shape w := Path.shape_map (headMap i) w
  simp only [partialNormal,hshape]
  split
  · rfl
  · rw [preprocess_map i blank rep rep' hr hi]
    simp only [List.map_map,Function.comp_def,classify_map i blank hi]
    have he := List.map_map (f := classify (Q := Q) (Γ := Γ) blank)
      (g := Sum.map (List.map (letterMap (S := S) (Γ := Γ) i)) (id : List S → List S))
      (l := preprocess blank rep (p,w))
    simp only [Function.comp_def] at he
    rw [←he,RawRuns.partialSource_map]
    simp only [Part.map_map]
    congr 1
    funext l
    simp only [List.flatMap_map,List.map_flatMap,Function.comp_def,realize_map]

end FiniteAlgebraicEnvelopes.Compiler.Word.Uniform

namespace FiniteAlgebraicEnvelopes.Compiler
open HeadCodec
open scoped HeadCodec
variable {P S Γ Q : Type*} [Primcodable P] [Primcodable Q]
  [Fintype S] [Fintype Γ] [Fintype Q]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [LinearOrder (Control.Sector S Γ Q)]
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)

namespace Surface.Uniform
omit [Primcodable P] [Primcodable Q] in
theorem preprocess_specialize (p : P) (v : Surface.Sector S Γ (Control.Head S Q)) :
    preprocess A.blank (fun x : P × Control.Sector S Γ Q => Control.representative A M x.2) (p,v) =
      Surface.preprocess A M v := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> rfl
end Surface.Uniform

namespace Word.Uniform
omit [Primcodable P] [Primcodable Q] in
theorem sectorPreprocess_specialize (p : P) (v : Word.Sector S Γ Q) :
    sectorPreprocess A.blank (fun x : P × Control.Sector S Γ Q => Control.representative A M x.2) (p,v) =
      Word.sectorPreprocess A M v := by
  simp only [sectorPreprocess,Surface.Uniform.preprocess_specialize,Word.sectorPreprocess]

omit [Primcodable P] [Primcodable Q] in
theorem preprocess_specialize (p : P) (w : List (Word.Letter S Γ Q)) :
    preprocess A.blank (fun x : P × Control.Sector S Γ Q => Control.representative A M x.2) (p,w) =
      Word.preprocess A M w := by
  simp only [preprocess,sectorPreprocess_specialize,Word.preprocess]

omit [Primcodable P] [Primcodable Q] in
theorem partialNormal_specialize (p : P) (f : List S → Part (List S)) (w : List (Word.Letter S Γ Q)) :
    partialNormal A.blank (fun x : P × Control.Sector S Γ Q => Control.representative A M x.2)
      (fun x => f x.2) (p,w)=Word.partialNormal A M f w := by
  simp only [partialNormal,Word.partialNormal,preprocess_specialize]
end Word.Uniform

end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

section
open Compiler Compiler.Simulator Compiler.HeadCodec ParameterMachine
open scoped Compiler.HeadCodec
variable {S T Γ Q : Type*} [Fintype T] [Fintype Γ] [Fintype Q]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable T] [Primcodable Γ] [Primcodable Q]
variable (A : Alphabet S Γ) (M : Machine Q Γ) (p : S) (B : Alphabet T (Bool×Γ))

noncomputable def codedNormal (f : ℕ × List T → Part (List T)) :
    ℕ × List (Compiler.Word.Letter T (Bool×Γ) (Control Q)) → Part (List (Compiler.Word.Letter T (Bool×Γ) (Control Q))) :=
  Compiler.Word.Uniform.partialNormal B.blank (codedRepresentative A M p B) f

theorem partrec_codedNormal {f : ℕ × List T → Part (List T)} (hf : Partrec f) :
    Partrec (codedNormal A M p B f) :=
  Compiler.Word.Uniform.partrec_partialNormal B.blank _ (primrec_codedRepresentative A M p B) hf

omit [Primcodable T] [Primcodable Γ] in
theorem codedNormal_map (n : ℕ) (f : ℕ × List T → Part (List T))
    (w : List (Compiler.Word.Letter T (Bool×Γ) (State Q n))) :
    letI := finiteOrder (T := T) (Γ := Γ) (Q := Q) n
    codedNormal A M p B f (n,w.map (Compiler.Word.letterMap (encode n)))=
      (Compiler.Word.partialNormal B (machine A M p n) (fun u => f (n,u)) w).map
        (List.map (Compiler.Word.letterMap (encode n))) := by
  let : Primcodable (State Q n) := Effect.finitePrimcodable _
  let := finiteOrder (T := T) (Γ := Γ) (Q := Q) n
  have h := Compiler.Word.Uniform.partialNormal_map (P := Unit) (encode n) B.blank
    (fun x => Compiler.Control.representative B (machine A M p n) x.2)
    (fun x => codedRepresentative A M p B (n,x.2))
    (fun _ v => codedRepresentative_map A M p B n v)
    (encode_injective n) (fun x => f (n,x.2)) () w
  rw [Compiler.Word.Uniform.partialNormal_specialize B (machine A M p n) () (fun u => f (n,u)) w] at h
  exact h

end

open Compiler Compiler.HeadCodec ParameterMachine
open scoped Compiler.HeadCodec
variable {T Γ Q : Type*} [Fintype T] [Fintype Γ] [Fintype Q]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Q] [Primcodable Q]

noncomputable def surfaces (n : ℕ) : List (Surface.Head (Compiler.Control.Head T (Control Q))) :=
  [.raw,.pending,.cleanup] ++ (heads n).map Surface.Head.internal

noncomputable def letters (n : ℕ) : List (Word.Letter T (Bool×Γ) (Control Q)) :=
  [.zero,.enter,.leave] ++
  (Scan.finiteList (Word.Cell T (Bool×Γ))).map Path.Letter.left ++
  (Scan.finiteList (Word.Cell T (Bool×Γ))).map Path.Letter.right ++
  (surfaces n).map Path.Letter.head

omit [DecidableEq T] [DecidableEq Q] in
theorem primrec_surfaces : Primrec (surfaces (T := T) (Q := Q)) :=
  Primrec.list_append.comp (Primrec.const _) (Primrec.list_map primrec_heads
    (primrec_internal.comp Primrec.snd).to₂)

omit [DecidableEq T] [DecidableEq Γ] [DecidableEq Q] in
theorem primrec_letters : Primrec (letters (T := T) (Γ := Γ) (Q := Q)) :=
  Primrec.list_append.comp (Primrec.const _)
    (Primrec.list_map primrec_surfaces (Path.Uniform.primrec_head.comp Primrec.snd).to₂)

omit [DecidableEq T] [DecidableEq Q] [Primcodable Q] in
theorem mem_surfaces_iff (n : ℕ) (h : Surface.Head (Compiler.Control.Head T (Control Q))) :
    h∈surfaces n ↔ ∃ a : Surface.Head (Compiler.Control.Head T (State Q n)),
      Surface.headMap (controlMap (encode n)) a=h := by
  cases h with
  | raw =>
    constructor
    · intro _; exact ⟨.raw,rfl⟩
    · intro _; simp [surfaces]
  | pending =>
    constructor
    · intro _; exact ⟨.pending,rfl⟩
    · intro _; simp [surfaces]
  | cleanup =>
    constructor
    · intro _; exact ⟨.cleanup,rfl⟩
    · intro _; simp [surfaces]
  | internal q =>
    simp only [surfaces,List.mem_append,List.mem_cons,List.mem_map,
      Surface.Head.internal.injEq,reduceCtorEq,List.not_mem_nil,false_or,exists_eq_right,mem_heads_iff]
    constructor
    · rintro ⟨a,ha⟩; exact ⟨.internal a,congrArg Surface.Head.internal ha⟩
    · rintro ⟨a,ha⟩
      cases a with
      | internal b => exact ⟨b,Surface.Head.internal.inj ha⟩
      | _ => cases ha

omit [DecidableEq T] [DecidableEq Γ] [DecidableEq Q] [Primcodable Q] in
theorem mem_letters_iff (n : ℕ) (h : Word.Letter T (Bool×Γ) (Control Q)) :
    h∈letters n ↔ ∃ a : Word.Letter T (Bool×Γ) (State Q n), Word.letterMap (encode n) a=h := by
  constructor
  · intro hh
    cases h with
    | zero => exact ⟨.zero,rfl⟩
    | enter => exact ⟨.enter,rfl⟩
    | leave => exact ⟨.leave,rfl⟩
    | left c => exact ⟨.left c,rfl⟩
    | right c => exact ⟨.right c,rfl⟩
    | head h =>
      have hm : h∈surfaces n := by simpa [letters] using hh
      obtain ⟨a,rfl⟩ := (mem_surfaces_iff n h).mp hm
      exact ⟨.head a,rfl⟩
  · rintro ⟨a,rfl⟩
    cases a with
    | head a =>
      have hm := (mem_surfaces_iff n (Surface.headMap (controlMap (encode n)) a)).mpr ⟨a,rfl⟩
      simpa [letters,Word.letterMap,Word.headMap,Path.mapLetter] using hm
    | _ => simp [letters,Word.letterMap,Path.mapLetter,Scan.mem_finiteList]

end FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

end OAI
