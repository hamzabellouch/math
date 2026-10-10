import OAI.ModelTheory.Choiceless.TableMachine

namespace OAI

namespace CPTSeparation.MatrixProgram

section

open Bounded TableMachine CounterLang

structure Control where
 active : Bool
 member : Bool
 test : Bool
 acc : Scalar
 deriving DecidableEq, Fintype

abbrev Prog := Bounded.Program Control

local infixr:60 " ;; " => Bounded.Program.seq

def ctrl (b : Bool) : Control := ⟨b,false,false,0⟩

def memberCode : Prog :=
 .cell .Cf .a .a (fun c b => {c with member := b}) ;;
 .cell .VB .t .a (fun c b => {c with member := c.member && b})

def coefficientStep : Prog :=
 .cell .Ed .x .x (fun c b => {c with test := b}) ;;
 .cell .I .a .x (fun c b => {c with test := c.test && b}) ;;
 .cell (.Z 1) .y .x (fun c b => {c with acc := c.acc + if c.test && b then 1 else 0}) ;;
 .cell (.Z 2) .y .x (fun c b => {c with acc := c.acc + if c.test && b then 2 else 0}) ;;
 .load (fun c => {c with test := false})

def coefficientCode : Prog :=
 .load (fun c => {c with acc := 0}) ;; .loop .x coefficientStep

def incidentStepX : Prog :=
 .cell .Ed .x .x (fun c b => {c with test := b}) ;;
 .cell .I .a .x (fun c b => {c with test := c.test && b}) ;;
 .cell .EB .y .x (fun c b => {c with test := c.test && b}) ;;
 .load (fun c => {c with active := c.active || (c.member && c.test),test := false})

def incidentStepA : Prog :=
 memberCode ;; .loop .x incidentStepX ;; .load (fun c => {c with member := false})

def incidentCode : Prog := .load (fun _ => ctrl false) ;; .loop .a incidentStepA

def normColumn : Prog := memberCode ;;
 .emit (fun c => some (if c.active && c.member then 1 else 0)) ;;
 .load (fun c => {c with member := false})

def lambdaColumn : Prog := memberCode ;; coefficientCode ;;
 .emit (fun c => some (if c.active && c.member then -c.acc else 0)) ;;
 .load (fun c => {c with member := false,acc := 0})

def muColumn : Prog :=
 .equal .z .y (fun c b => {c with test := b}) ;;
 .emit (fun c => some (if c.active && c.test then 1 else 0)) ;;
 .load (fun c => {c with test := false})

def normRowCode : Prog :=
 .cell .Cf .t .t (fun _ b => ctrl b) ;;
 .loop .a normColumn ;;
 .loop .z (.emit (fun _ => some 0)) ;;
 .emit (fun c => some (if c.active then 1 else 0)) ;;
 .emit (fun _ => none) ;;
 .load (fun _ => ctrl false)

def consRowCode : Prog :=
 incidentCode ;;
 .cell .Cf .t .t (fun c b => {c with active := c.active && b}) ;;
 .cell .Ed .y .y (fun c b => {c with active := c.active && b}) ;;
 .loop .a lambdaColumn ;;
 .loop .z muColumn ;;
 .emit (fun _ => some 0) ;;
 .emit (fun _ => none) ;;
 .load (fun _ => ctrl false)

def program : Prog :=
 .load (fun _ => ctrl false) ;;
 .loop .t normRowCode ;;
 .loop .t (.loop .y consRowCode)

lemma program_wf : program.WF ∅ := by
 simp [program,normRowCode,consRowCode,normColumn,lambdaColumn,muColumn,
   memberCode,coefficientCode,coefficientStep,incidentCode,incidentStepA,incidentStepX,
   Bounded.Program.WF]

def member (rel : Relation) (t a : ℕ) : Bool := rel .Cf a a && rel .VB t a

def contribution (rel : Relation) (y a x : ℕ) : Scalar :=
 if rel .Ed x x && rel .I a x then
   (if rel (.Z 1) y x then 1 else 0)+(if rel (.Z 2) y x then 2 else 0) else 0

def coefficient (N : ℕ) (rel : Relation) (y a : ℕ) : Scalar :=
 ((List.range N).map (contribution rel y a)).sum

def edgeTest (rel : Relation) (y a x : ℕ) : Bool :=
 rel .Ed x x && rel .I a x && rel .EB y x

def incident (N : ℕ) (rel : Relation) (t y : ℕ) : Bool :=
 (List.range N).any fun a => member rel t a && (List.range N).any (edgeTest rel y a)

def normChunk (N : ℕ) (rel : Relation) (t : ℕ) : List Letter :=
 (List.range N).map (fun a => some (if rel .Cf t t && member rel t a then 1 else 0)) ++
 List.replicate N (some 0) ++ [some (if rel .Cf t t then 1 else 0),none]

def consActive (N : ℕ) (rel : Relation) (t y : ℕ) : Bool :=
 (incident N rel t y && rel .Cf t t) && rel .Ed y y

def consChunk (N : ℕ) (rel : Relation) (t y : ℕ) : List Letter :=
 (List.range N).map (fun a => some (if consActive N rel t y && member rel t a then -coefficient N rel y a else 0)) ++
 (List.range N).map (fun z => some (if consActive N rel t y && (z==y) then 1 else 0)) ++ [some 0,none]

def matrix (N : ℕ) (rel : Relation) : List Letter :=
 (List.range N).flatMap (normChunk N rel) ++
 (List.range N).flatMap (fun t => (List.range N).flatMap (consChunk N rel t))

end

section

open Bounded TableMachine CounterLang

lemma interp_seq {V} (a b : Bounded.Program V) (N : ℕ) (rel : Relation) (e) (s) :
 (Bounded.Program.seq a b).interpret N rel e s = b.interpret N rel e (a.interpret N rel e s) := rfl

lemma interp_load {V} (f : V → V) (N : ℕ) (rel : Relation) (e) (s) :
 (Bounded.Program.load f).interpret N rel e s = (f s.1,s.2) := rfl

lemma interp_cell {V} (r i j) (f : V → Bool → V) (N : ℕ) (rel : Relation) (e) (s) :
 (Bounded.Program.cell r i j f).interpret N rel e s = (f s.1 (rel r (e i) (e j)),s.2) := rfl

lemma interp_emit {V} (f : V → Letter) (N : ℕ) (rel : Relation) (e) (s) :
 (Bounded.Program.emit f).interpret N rel e s = (s.1,f s.1::s.2) := rfl

lemma memberCode_spec (N : ℕ) (rel : Relation) (e : Index → ℕ) (c : Control) (out) :
 memberCode.interpret N rel e (c,out) = ({c with member := member rel (e .t) (e .a)},out) := rfl

lemma coefficientStep_spec (N : ℕ) (rel : Relation) (e : Index → ℕ) (act mem : Bool) (acc : Scalar) (out) :
 coefficientStep.interpret N rel e (⟨act,mem,false,acc⟩,out) =
   (⟨act,mem,false,acc+contribution rel (e .y) (e .a) (e .x)⟩,out) := by
 simp only [coefficientStep,Bounded.Program.interpret,contribution]
 by_cases h : (rel .Ed (e .x) (e .x) && rel .I (e .a) (e .x)) = true <;>
   simp only [Bool.and_eq_true] at h ⊢ <;> simp [h,add_assoc]

lemma coefficient_fold_spec (N : ℕ) (rel : Relation) (e : Index → ℕ)
    (ls : List ℕ) (act mem : Bool) (acc : Scalar) (out) :
 ls.foldl (fun s k => coefficientStep.interpret N rel (Function.update e .x k) s)
    (⟨act,mem,false,acc⟩,out) =
   (⟨act,mem,false,acc+(ls.map (contribution rel (e .y) (e .a))).sum⟩,out) := by
 induction ls generalizing acc with
 | nil => simp
 | cons a ls ih =>
   rw [List.foldl_cons,coefficientStep_spec]
   simp only [Function.update_self,Function.update_of_ne (show Index.y ≠ .x by decide),
      Function.update_of_ne (show Index.a ≠ .x by decide)]
   rw [ih]
   simp [add_assoc]

lemma coefficientCode_spec (N : ℕ) (rel : Relation) (e : Index → ℕ) (act mem : Bool) (acc : Scalar) (out) :
 coefficientCode.interpret N rel e (⟨act,mem,false,acc⟩,out) =
   (⟨act,mem,false,coefficient N rel (e .y) (e .a)⟩,out) := by
 simp only [coefficientCode,Bounded.Program.interpret]
 exact (coefficient_fold_spec N rel e (List.range N) act mem 0 out).trans (by simp [coefficient])

lemma incidentStepX_spec (N : ℕ) (rel : Relation) (e : Index → ℕ) (act mem : Bool) (out) :
 incidentStepX.interpret N rel e (⟨act,mem,false,0⟩,out) =
   (⟨act || (mem && edgeTest rel (e .y) (e .a) (e .x)),mem,false,0⟩,out) := rfl

lemma incident_fold_x (N : ℕ) (rel : Relation) (e : Index → ℕ)
    (ls : List ℕ) (act mem : Bool) (out) :
 ls.foldl (fun s k => incidentStepX.interpret N rel (Function.update e .x k) s)
    (⟨act,mem,false,0⟩,out) =
   (⟨act || (mem && ls.any (edgeTest rel (e .y) (e .a))),mem,false,0⟩,out) := by
 induction ls generalizing act with
 | nil => simp
 | cons a ls ih =>
   rw [List.foldl_cons,incidentStepX_spec]
   simp only [Function.update_self,Function.update_of_ne (show Index.y ≠ .x by decide),
      Function.update_of_ne (show Index.a ≠ .x by decide)]
   rw [ih]
   cases act <;> cases mem <;> simp []

lemma incidentStepA_spec (N : ℕ) (rel : Relation) (e : Index → ℕ) (act : Bool) (out) :
 incidentStepA.interpret N rel e (ctrl act,out) =
   (ctrl (act || (member rel (e .t) (e .a) && (List.range N).any (edgeTest rel (e .y) (e .a)))),out) := by
 simp only [incidentStepA,interp_seq,memberCode_spec,ctrl]

 simp only [Bounded.Program.interpret]
 rw [incident_fold_x]

lemma incident_fold_a (N : ℕ) (rel : Relation) (e : Index → ℕ)
    (ls : List ℕ) (act : Bool) (out) :
 ls.foldl (fun s k => incidentStepA.interpret N rel (Function.update e .a k) s)
    (ctrl act,out) =
   (ctrl (act || ls.any (fun a => member rel (e .t) a &&
     (List.range N).any (edgeTest rel (e .y) a))),out) := by
 induction ls generalizing act with
 | nil => simp
 | cons a ls ih =>
   rw [List.foldl_cons,incidentStepA_spec]
   simp only [Function.update_self,Function.update_of_ne (show Index.y ≠ .a by decide),
      Function.update_of_ne (show Index.t ≠ .a by decide)]
   rw [ih]
   simp [Bool.or_assoc]

lemma incidentCode_spec (N : ℕ) (rel : Relation) (e : Index → ℕ) (c : Control) (out) :
 incidentCode.interpret N rel e (c,out) =
   (ctrl (incident N rel (e .t) (e .y)),out) := by
 simp only [incidentCode,Bounded.Program.interpret]
 rw [incident_fold_a]
 simp [incident]

lemma normColumn_spec (N : ℕ) (rel : Relation) (e : Index → ℕ) (act : Bool) (out) :
 normColumn.interpret N rel e (ctrl act,out) =
   (ctrl act,some (if act && member rel (e .t) (e .a) then 1 else 0)::out) := by
 simp only [normColumn,Bounded.Program.interpret,memberCode_spec]
 rfl

lemma lambdaColumn_spec (N : ℕ) (rel : Relation) (e : Index → ℕ) (act : Bool) (out) :
 lambdaColumn.interpret N rel e (ctrl act,out) =
   (ctrl act,some (if act && member rel (e .t) (e .a) then -coefficient N rel (e .y) (e .a) else 0)::out) := by
 simp only [lambdaColumn,interp_seq,memberCode_spec,ctrl]
 rw [coefficientCode_spec]
 rfl

lemma muColumn_spec (N : ℕ) (rel : Relation) (e : Index → ℕ) (act : Bool) (out) :
 muColumn.interpret N rel e (ctrl act,out) =
   (ctrl act,some (if act && (e .z == e .y) then 1 else 0)::out) := rfl

lemma normRowCode_spec (N : ℕ) (rel : Relation) (e : Index → ℕ) (c : Control) (out) :
 normRowCode.interpret N rel e (c,out) =
   (ctrl false,(normChunk N rel (e .t)).reverse++out) := by
 have ha := loop_emits N rel normColumn .a e (ctrl (rel .Cf (e .t) (e .t)))
   (fun a => [some (if rel .Cf (e .t) (e .t) && member rel (e .t) a then 1 else 0)])
   (by intro k hk o; simpa [Function.update] using normColumn_spec N rel (Function.update e .a k) (rel .Cf (e .t) (e .t)) o) out
 have hz (o) := loop_emits N rel (.emit (fun _ : Control => some 0)) .z e (ctrl (rel .Cf (e .t) (e .t)))
   (fun _ => [some 0]) (by intro k hk z; rfl) o
 simp only [normRowCode,interp_seq,interp_cell]
 rw [ha,hz]
 simp [interp_emit,interp_load,normChunk,List.reverse_append,List.append_assoc,← List.map_eq_flatMap,ctrl]

lemma consRowCode_spec (N : ℕ) (rel : Relation) (e : Index → ℕ) (c : Control) (out) :
 consRowCode.interpret N rel e (c,out) =
   (ctrl false,(consChunk N rel (e .t) (e .y)).reverse++out) := by
 let act := consActive N rel (e .t) (e .y)
 have ha (o) := loop_emits N rel lambdaColumn .a e (ctrl act)
   (fun a => [some (if act && member rel (e .t) a then -coefficient N rel (e .y) a else 0)])
   (by intro k hk z; simpa [Function.update] using lambdaColumn_spec N rel (Function.update e .a k) act z) o
 have hz (o) := loop_emits N rel muColumn .z e (ctrl act)
   (fun z => [some (if act && (z==e .y) then 1 else 0)])
   (by intro k hk z; simpa [Function.update] using muColumn_spec N rel (Function.update e .z k) act z) o
 simp only [consRowCode,interp_seq,incidentCode_spec,interp_cell,ctrl]
 dsimp [ctrl,act,consActive] at ha hz
 rw [ha,hz]
 simp [interp_emit,interp_load,consChunk,consActive,List.reverse_append,List.append_assoc,← List.map_eq_flatMap]

lemma program_spec (N : ℕ) (rel : Relation) (e : Index → ℕ) (c : Control) (out) :
 program.interpret N rel e (c,out) = (ctrl false,(matrix N rel).reverse++out) := by
 have hn := loop_emits N rel normRowCode .t e (ctrl false) (normChunk N rel)
   (by intro k hk o; simpa [Function.update] using normRowCode_spec N rel (Function.update e .t k) (ctrl false) o) out
 have hc (o) := loop_emits N rel (.loop .y consRowCode) .t e (ctrl false)
   (fun t => (List.range N).flatMap (consChunk N rel t))
   (by
     intro t ht o
     apply loop_emits
     intro y hy z
     simpa [Function.update] using consRowCode_spec N rel
       (Function.update (Function.update e .t t) .y y) (ctrl false) z) o
 simp only [program,interp_seq,interp_load]
 rw [hn,hc]
 simp [matrix,List.reverse_append,List.append_assoc]

end

open Bounded TableMachine

lemma range_eq_finRange_map (N : ℕ) : List.range N = (List.finRange N).map Fin.val := by
 apply List.ext_getElem
 · simp
 · intro i hi hj
   simp

lemma range_map_eq {α} (N : ℕ) (f : ℕ → α) :
 (List.range N).map f = List.ofFn (fun i : Fin N => f i) := by
 rw [range_eq_finRange_map,List.map_map, List.ofFn_eq_map]
 rfl

lemma range_flatMap_eq {α} (N : ℕ) (f : ℕ → List α) :
 (List.range N).flatMap f = (List.finRange N).flatMap (fun i : Fin N => f i) := by
 rw [range_eq_finRange_map,List.flatMap_map]

lemma ofFn_addCases {α : Type} {m n : ℕ} (f : Fin m → α) (g : Fin n → α) :
 List.ofFn (Fin.addCases f g) = List.ofFn f ++ List.ofFn g := by
 have he : Fin.addCases f g = Fin.append f g := by
   funext i
   refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
 rw [he,List.ofFn_fin_append]

lemma sum_scalar_three (f : Scalar → Scalar) : (∑ δ, f δ) = f 0+f 1+f 2 := by
 have h : (Finset.univ : Finset Scalar) = {0,1,2} := by decide
 change Finset.sum Finset.univ f = _
 rw [h]
 rw [Finset.sum_insert (by decide : (0:Scalar) ∉ ({1,2} : Finset Scalar)),
   Finset.sum_insert (by decide : (1:Scalar) ∉ ({2} : Finset Scalar)),Finset.sum_singleton]
 ring

variable {N : ℕ} (S : OrderedQuery.Data N) (rel : Relation)

variable (reads : ∀ (r : Symbol) (a b : Fin N), rel r a b = S.rel r a b)

include reads

lemma contribution_eq (y a x : Fin N) :
 contribution rel y a x = if S.rel .Ed x x ∧ S.rel .I a x then
   ∑ δ : Scalar, if S.rel (.Z δ) y x then δ else 0 else 0 := by
 simp only [contribution,reads,Bool.and_eq_true,sum_scalar_three]
 simp

lemma coefficient_eq_ordered (y a : Fin N) : coefficient N rel y a = OrderedQuery.coefficient S y a := by
 rw [coefficient,range_map_eq]
 simp only [contribution_eq S rel reads,List.sum_ofFn,OrderedQuery.coefficient]

lemma incident_eq_ordered (t y : Fin N) : incident N rel t y = OrderedQuery.incident S t y := by
 simp only [incident,range_eq_finRange_map,List.any_map,Function.comp_def,member,edgeTest,
   reads,OrderedQuery.incident]

lemma normChunk_eq (t : Fin N) : normChunk N rel t =
 (SerialGaussian.Row.encode (OrderedQuery.normalizationRow S t)).coeff.map some ++
   [some (OrderedQuery.normalizationRow S t).rhs,none] := by
 have hr : ∀ (a : Fin N), member rel t a = (S.rel .Cf a a && S.rel .VB t a) := by
   intro a; simp [member,reads]
 simp only [normChunk,reads,range_map_eq,SerialGaussian.Row.encode,OrderedQuery.normalizationRow]
 by_cases ht : S.rel .Cf t t = true
 · simp only [ht,ite_true,Bool.true_and,hr]
   simp [ofFn_addCases,List.map_ofFn,List.map_append,Function.comp_def]
 · have hf : S.rel .Cf t t = false := Bool.eq_false_iff.mpr ht
   simp [hf,]

lemma consActive_eq (t y : Fin N) : consActive N rel t y =
 (S.rel .Cf t t && S.rel .Ed y y && OrderedQuery.incident S t y) := by
 rw [consActive,incident_eq_ordered S rel reads,reads,reads]
 cases S.rel .Cf t t <;> cases S.rel .Ed y y <;> cases OrderedQuery.incident S t y <;> rfl

lemma consChunk_eq (t y : Fin N) : consChunk N rel t y =
 (SerialGaussian.Row.encode (OrderedQuery.consistencyRow S t y)).coeff.map some ++
   [some (OrderedQuery.consistencyRow S t y).rhs,none] := by
 have hr : ∀ (a : Fin N), member rel t a = (S.rel .Cf a a && S.rel .VB t a) := by
   intro a; simp [member,reads]
 simp only [consChunk,consActive_eq S rel reads,range_map_eq,
   SerialGaussian.Row.encode,OrderedQuery.consistencyRow]
 by_cases ht : (S.rel .Cf t t && S.rel .Ed y y && OrderedQuery.incident S t y) = true
 · simp only [ht,ite_true,Bool.true_and,hr,coefficient_eq_ordered S rel reads]
   simp [ofFn_addCases,List.map_append,List.map_ofFn,Function.comp_def,beq_iff_eq,Fin.val_inj]
 · have hf : (S.rel .Cf t t && S.rel .Ed y y && OrderedQuery.incident S t y) = false := Bool.eq_false_iff.mpr ht
   simp [hf,]

lemma matrix_eq_payload : matrix N rel = SerialGaussian.payload (SerialGaussian.queryRows S) := by
 simp only [matrix,range_flatMap_eq,normChunk_eq S rel reads,consChunk_eq S rel reads,
   SerialGaussian.queryRows,OrderedQuery.rows,SerialGaussian.payload,List.map_append,
   List.flatMap_append,List.flatMap_map,List.map_flatMap,List.flatMap_assoc]
 rfl

omit reads in
lemma matrix_input {N : ℕ} (S : OrderedQuery.Data N) :
 matrix N (readTable N (tableInput S)) = SerialGaussian.payload (SerialGaussian.queryRows S) :=
 matrix_eq_payload S _ (readTable_input S)

end CPTSeparation.MatrixProgram

end OAI
