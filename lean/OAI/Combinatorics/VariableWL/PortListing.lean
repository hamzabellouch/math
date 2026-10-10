import OAI.Combinatorics.VariableWL.Descriptor

namespace OAI

universe uVariable1 uVariable2

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

def underTwo (P : Expr (n+2)) : Expr (n+3) :=
  P.reindex (Fin.cons 0 (Fin.cons 1 (fun i=>i.succ.succ.succ)))

theorem underTwo_value (P : Expr (n+2)) (v : Env n) (a b c : Word) :
    (underTwo P).value (cons a (cons b (cons c v)))=P.value (cons a (cons b v)) := by
  apply congrArg P.program.value
  funext i
  exact Fin.cases rfl (fun i=>Fin.cases rfl (fun _=>rfl) i) i

theorem underTwo_bit (P : Expr (n+2)) (v : Env n) (a b c : Word) :
    (underTwo P).bit (cons a (cons b (cons c v)))=P.bit (cons a (cons b v)) := by
  unfold Expr.bit
  rw [underTwo_value]

theorem apply₂_bit (F : Expr (n+2)) (A B : Expr n) (v : Env n) :
    (apply₂ F A B).bit v=F.bit (cons (A.value v) (cons (B.value v) v)) := by
  unfold Expr.bit
  rw [apply₂_value]

theorem count_value (N : Expr n) (P : Expr (n+1)) (v : Env n) :
    (count N P).value v=List.replicate ((count N P).number v) true := by
  change (Recipe.countTrue N.program P.program).value v=_
  rw [Recipe.countTrue_value,count_number]
  rfl

theorem select_value (N : Expr n) (P : Expr (n+1)) (I : Expr n) (v : Env n) :
    (select N P I).value v=List.replicate (Descriptor.pick (N.number v)
      (fun j=>P.bit (cons (List.replicate j true) v)) (I.number v)) true := by
  rw [select,count_value]
  change List.replicate ((select N P I).number v) true=_
  rw [select_number]

structure GraphListing (n : ℕ) where
  bound : Expr n
  valid : Expr (n+1)
  edge : Expr (n+2)

def GraphListing.eval (D : GraphListing n) (v : Env n) : Descriptor.Data where
  bound := D.bound.number v
  valid := fun j=>D.valid.bit (cons (List.replicate j true) v)
  edge := fun i j=>D.edge.bit (cons (List.replicate i true) (cons (List.replicate j true) v))

def GraphListing.order (D : GraphListing n) : Expr n := count D.bound D.valid

theorem GraphListing.order_number (D : GraphListing n) (v : Env n) :
    D.order.number v=Descriptor.rank (D.eval v).valid (D.eval v).bound := count_number ..

def GraphListing.matrix (D : GraphListing n) : Expr n :=
  collect (mul D.order D.order) (apply₂ (underTwo D.edge)
    (select D.bound.up (underOne D.valid) (div (input 0) D.order.up))
    (select D.bound.up (underOne D.valid) (mod (input 0) D.order.up)))

theorem GraphListing.matrix_value (D : GraphListing n) (v : Env n) :
    D.matrix.value v=NumericPromise.pack (D.order.number v) (fun i j=>
      (D.eval v).edge (Descriptor.pick (D.eval v).bound (D.eval v).valid i)
        (Descriptor.pick (D.eval v).bound (D.eval v).valid j)) := by
  simp only [GraphListing.matrix,collect_value,mul_number,apply₂_bit,select_value,
    up_number,div_number,mod_number,input_number,cons_zero,List.length_replicate,underOne_bit,underTwo_bit]
  rfl

theorem GraphListing.matrix_correct (D : GraphListing n) (v : Env n) (h : (D.eval v).Sound) :
    D.matrix.value v=Encoding.matrix ((D.eval v).graph h) := by
  classical
  rw [D.matrix_value,Encoding.matrix]
  apply List.ext_getElem
  · simp only [NumericPromise.pack,List.length_map,List.length_range,List.length_ofFn,
      Descriptor.Data.graph,D.order_number]
  · intro i hi hi'
    simp only [NumericPromise.pack,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    rw [D.order_number]
    simp only [Descriptor.Data.graph,Fin.divNat,Fin.modNat]
    exact Bool.decide_eq_true.symm

def GraphListing.code (D : GraphListing n) : Expr n := graphEncode D.order D.matrix

theorem GraphListing.code_correct (D : GraphListing n) (v : Env n) (h : (D.eval v).Sound) :
    D.code.value v=graphCode ((D.eval v).graph h) :=
  graphEncode_value _ _ _ _ (D.order_number v) (D.matrix_correct v h)

theorem outputs (P : Expr 1) : ∃M : VariableWL.Machine,∃c d : ℕ,∀w : Word,
    OutputsWithin M w (P.value (fun _=>w.reverse)) (c*(w.length+1)^d) := by
  obtain ⟨M,hM⟩ := Recipe.outputs P.program
  obtain ⟨f,hf,hP⟩ := P.polynomial
  obtain ⟨c,d,hcd⟩ := ((Growth.constant 4).mul ((Growth.ident.add hf).add (Growth.constant 1)))
  refine ⟨M,c,d,fun w=>?_⟩
  have ht := hP w.length (fun _=>w.reverse) (fun _=>by simp)
  obtain ⟨t,htime,hh,ho⟩ := hM w
  refine ⟨t,htime.trans (le_trans ?_ (hcd w.length)),hh,ho⟩
  have hp : P.program.time (fun _=>w.reverse)≤f w.length := by omega
  dsimp only [id]
  exact Nat.mul_le_mul_left 4 (by omega)

theorem reduces (P : Expr 1) (L R : Language)
    (h : ∀w : Word,w∈L ↔ P.value (fun _=>w.reverse)∈R) : PolytimeReduces L R := by
  obtain ⟨M,c,d,hP⟩ := outputs P
  exact ⟨M,c,d,fun w=>⟨P.value (fun _=>w.reverse),hP w,h w⟩⟩

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Descriptor
open SubcubicRealization
attribute [local instance] Classical.propDecidable

structure Presentation (A : Type uVariable1) where
  bound : ℕ
  valid : ℕ → Bool
  equiv : Valid bound valid ≃ A

namespace Presentation
variable {A : Type uVariable2} (D : Presentation A)
def encode (a : A) : ℕ := (D.equiv.symm a).val.val

theorem encode_lt (a : A) : D.encode a<D.bound := (D.equiv.symm a).val.isLt
theorem encode_valid (a : A) : D.valid (D.encode a)=true := (D.equiv.symm a).property

theorem encode_injective : Function.Injective D.encode := by
  intro a b h
  apply D.equiv.symm.injective
  apply Subtype.ext
  exact Fin.ext h

@[instance_reducible] noncomputable def numbering [Fintype A] : FiniteNumbering A :=
  ⟨D.equiv.symm.trans ((rankEquiv D.bound D.valid).trans (finCongr (by
    simpa only [Fintype.card_fin] using (Fintype.card_congr (rankEquiv D.bound D.valid)).symm.trans
      (Fintype.card_congr D.equiv))))⟩

end Presentation

@[ext] structure PortData where
  bound : ℕ
  valid : ℕ → Bool
  color : ℕ → ℕ
  colorBound : ℕ
  incidence : ℕ → ℕ → Bool

namespace PortData
abbrev Owners (D : PortData) := Valid D.bound D.valid

def Sound (D : PortData) : Prop :=
  (∀a : D.Owners,D.color a.val.val≤D.colorBound) ∧
  (∀a b : D.Owners,∀i j : Fin 3,
    D.incidence (3*a.val.val+i.val) (3*b.val.val+j.val)=
      D.incidence (3*b.val.val+j.val) (3*a.val.val+i.val)) ∧
  (∀a b c : D.Owners,∀i j k : Fin 3,
    D.incidence (3*a.val.val+i.val) (3*b.val.val+j.val)=true →
    D.incidence (3*a.val.val+i.val) (3*c.val.val+k.val)=true → b=c ∧ j=k) ∧
  (∀a b : D.Owners,∀i j : Fin 3,
    D.incidence (3*a.val.val+i.val) (3*b.val.val+j.val)=true → a≠b)

noncomputable def ports (D : PortData) (h : D.Sound) : PortGraph D.Owners where
  edge x y := D.incidence (3*x.1.val.val+x.2.val) (3*y.1.val.val+y.2.val)=true
  symm := by intro x y he; rw [h.2.1]; exact he
  unique := by intro x y z hy hz; obtain ⟨ha,hb⟩ := h.2.2.1 _ _ _ _ _ _ hy hz; exact Prod.ext ha hb
  different := by intro x y he; exact h.2.2.2 _ _ _ _ he

abbrev Vertices (D : PortData) := Vertex (fun a : D.Owners=>D.color a.val.val)

def stride (D : PortData) : ℕ := D.colorBound+2
def owner (D : PortData) (i : ℕ) : ℕ := i/D.stride/3
def port (D : PortData) (i : ℕ) : ℕ := i/D.stride%3
def level (D : PortData) (i : ℕ) : ℕ := i%D.stride
def code (D : PortData) (x : D.Vertices) : ℕ := (3*x.owner.val.val+x.port.val)*D.stride+x.level

def expanded (D : PortData) : Data where
  bound := (3*D.bound)*D.stride
  valid i := D.valid (D.owner i) && decide (D.level i<D.color (D.owner i)+2)
  edge i j :=
    (decide (D.owner i=D.owner j) &&
      ((decide (D.level i=0) && decide (D.level j=0) && decide (D.port i≠D.port j)) ||
        (decide (D.port i=D.port j) &&
          (decide (D.level i+1=D.level j) || decide (D.level j+1=D.level i))))) ||
    (decide (D.level i=1) && decide (D.level j=1) &&
      D.incidence (3*D.owner i+D.port i) (3*D.owner j+D.port j))

theorem stride_pos (D : PortData) : 0<D.stride := by unfold stride; omega

theorem owner_lt (D : PortData) {i : ℕ} (hi : i<D.expanded.bound) : D.owner i<D.bound := by
  have h : i/D.stride<3*D.bound := (Nat.div_lt_iff_lt_mul D.stride_pos).mpr hi
  unfold owner
  apply (Nat.div_lt_iff_lt_mul (by omega : 0<3)).mpr
  simpa only [Nat.mul_comm] using h

theorem code_parts (D : PortData) (h : D.Sound) (x : D.Vertices) :
    D.owner (D.code x)=x.owner.val.val ∧ D.port (D.code x)=x.port.val ∧ D.level (D.code x)=x.level := by
  have hx : x.level<D.stride := lt_of_lt_of_le x.bound (Nat.add_le_add_right (h.1 x.owner) 2)
  have hp : x.port.val<3 := x.port.isLt
  have hd : D.code x/D.stride=3*x.owner.val.val+x.port.val := by
    rw [code,Nat.mul_comm _ D.stride,Nat.mul_add_div D.stride_pos,Nat.div_eq_of_lt hx,Nat.add_zero]
  constructor
  · change (D.code x/D.stride)/3=_
    rw [hd,Nat.mul_add_div (by omega : 0<3),Nat.div_eq_of_lt hp,Nat.add_zero]
  constructor
  · change (D.code x/D.stride)%3=_
    rw [hd,Nat.mul_add_mod,Nat.mod_eq_of_lt hp]
  · change D.code x%D.stride=_
    rw [code,Nat.mul_comm _ D.stride,Nat.mul_add_mod,Nat.mod_eq_of_lt hx]

theorem code_lt (D : PortData) (h : D.Sound) (x : D.Vertices) : D.code x<D.expanded.bound := by
  have hx : x.level<D.stride := lt_of_lt_of_le x.bound (Nat.add_le_add_right (h.1 x.owner) 2)
  have hp : 3*x.owner.val.val+x.port.val<3*D.bound := by
    have := x.owner.val.isLt
    have := x.port.isLt
    omega
  exact (Nat.add_lt_add_left hx _).trans_le (by
    change (3*x.owner.val.val+x.port.val)*D.stride+D.stride≤(3*D.bound)*D.stride
    rw [←Nat.succ_mul]
    exact Nat.mul_le_mul_right _ hp)

noncomputable def presentation (D : PortData) (h : D.Sound) : Presentation D.Vertices where
  bound := D.expanded.bound
  valid := D.expanded.valid
  equiv := {
    toFun a := ⟨⟨⟨D.owner a.val.val,D.owner_lt a.val.isLt⟩,(Bool.and_eq_true_iff.mp a.property).1⟩,
      ⟨D.port a.val.val,Nat.mod_lt _ (by omega)⟩,D.level a.val.val,
      of_decide_eq_true (Bool.and_eq_true_iff.mp a.property).2⟩
    invFun x := ⟨⟨D.code x,D.code_lt h x⟩,by
      simp only [expanded,code_parts D h x |>.1,code_parts D h x |>.2.2,x.owner.property,
        x.bound,decide_true,Bool.and_self]⟩
    left_inv a := by
      apply Subtype.ext
      apply Fin.ext
      change (3*(a.val.val/D.stride/3)+(a.val.val/D.stride%3))*D.stride+a.val.val%D.stride=a.val.val
      rw [Nat.div_add_mod,Nat.mul_comm,Nat.div_add_mod]
    right_inv x := by
      apply Vertex.ext
      · apply Subtype.ext; apply Fin.ext; exact (code_parts D h x).1
      · apply Fin.ext; exact (code_parts D h x).2.1
      · exact (code_parts D h x).2.2 }

end PortData
end VariableWL.Descriptor

namespace VariableWL.Descriptor
@[ext] theorem data_ext {D E : Data} (hb : D.bound=E.bound) (hv : D.valid=E.valid)
    (he : D.edge=E.edge) : D=E := by cases D; cases E; cases hb; cases hv; cases he; rfl
end VariableWL.Descriptor

namespace VariableWL.Descriptor.PortData
open SubcubicRealization
attribute [local instance] Classical.propDecidable

 theorem edge_correct (D : PortData) (h : D.Sound) (a b : Valid D.expanded.bound D.expanded.valid) :
    D.expanded.edge a.val.val b.val.val=true ↔
      (graph (D.ports h) (fun x=>D.color x.val.val)).Adj
        ((D.presentation h).equiv a) ((D.presentation h).equiv b) := by
  change D.expanded.edge a.val.val b.val.val=true ↔
    ((⟨⟨D.owner a.val.val,D.owner_lt a.val.isLt⟩,
        (Bool.and_eq_true_iff.mp a.property).1⟩ : D.Owners)=
      ⟨⟨D.owner b.val.val,D.owner_lt b.val.isLt⟩,(Bool.and_eq_true_iff.mp b.property).1⟩ ∧
      ((D.level a.val.val=0 ∧ D.level b.val.val=0 ∧
        (⟨D.port a.val.val,Nat.mod_lt _ (by omega)⟩ : Fin 3)≠⟨D.port b.val.val,Nat.mod_lt _ (by omega)⟩) ∨
        ((⟨D.port a.val.val,Nat.mod_lt _ (by omega)⟩ : Fin 3)=⟨D.port b.val.val,Nat.mod_lt _ (by omega)⟩ ∧
          (D.level a.val.val+1=D.level b.val.val ∨ D.level b.val.val+1=D.level a.val.val)))) ∨
    (D.level a.val.val=1 ∧ D.level b.val.val=1 ∧
      D.incidence (3*D.owner a.val.val+D.port a.val.val) (3*D.owner b.val.val+D.port b.val.val)=true)
  simp only [expanded,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,
    Subtype.mk.injEq,ne_eq,Fin.ext_iff,and_assoc]

 theorem sound_expanded (D : PortData) (h : D.Sound) : D.expanded.Sound := by
  constructor
  · intro a b ha hb hva hvb
    let x : Valid D.expanded.bound D.expanded.valid := ⟨⟨a,ha⟩,hva⟩
    let y : Valid D.expanded.bound D.expanded.valid := ⟨⟨b,hb⟩,hvb⟩
    apply Bool.eq_iff_iff.mpr
    exact (D.edge_correct h x y).trans ((graph (D.ports h) (fun x=>D.color x.val.val)).adj_comm _ _ |>.trans
      (D.edge_correct h y x).symm)
  · intro a ha hva
    apply Bool.eq_false_iff.mpr
    intro he
    exact (graph (D.ports h) (fun x=>D.color x.val.val)).loopless.irrefl _
      ((D.edge_correct h ⟨⟨a,ha⟩,hva⟩ ⟨⟨a,ha⟩,hva⟩).mp he)

noncomputable def graphIso (D : PortData) (h : D.Sound) :
    (D.expanded.graph (D.sound_expanded h)).graph ≃g
      graph (D.ports h) (fun x=>D.color x.val.val) where
  toEquiv := (rankEquiv D.expanded.bound D.expanded.valid).symm.trans (D.presentation h).equiv
  map_rel_iff' := by
    intro x y
    exact (D.edge_correct h ((rankEquiv D.expanded.bound D.expanded.valid).symm x)
      ((rankEquiv D.expanded.bound D.expanded.valid).symm y)).symm

end VariableWL.Descriptor.PortData

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n m : ℕ}

theorem length_value (P : Expr n) (v : Env n) :
    (length P).value v=List.replicate (P.number v) true := Recipe.len_value ..

def applyNat (P : Expr (n+1)) (I : Expr n) : Expr n := (length I).bind P

theorem applyNat_value (P : Expr (n+1)) (I : Expr n) (v : Env n) :
    (applyNat P I).value v=P.value (cons (List.replicate (I.number v) true) v) := by
  rw [applyNat,bind_value,length_value]

theorem applyNat_bit (P : Expr (n+1)) (I : Expr n) (v : Env n) :
    (applyNat P I).bit v=P.bit (cons (List.replicate (I.number v) true) v) := by
  unfold Expr.bit
  rw [applyNat_value]

theorem applyNat_number (P : Expr (n+1)) (I : Expr n) (v : Env n) :
    (applyNat P I).number v=P.number (cons (List.replicate (I.number v) true) v) := by
  change ((applyNat P I).value v).length=_
  rw [applyNat_value]
  rfl

def applyNat₂ (P : Expr (n+2)) (I J : Expr n) : Expr n := applyNat (applyNat P I.up) J

theorem applyNat₂_bit (P : Expr (n+2)) (I J : Expr n) (v : Env n) :
    (applyNat₂ P I J).bit v=P.bit (cons (List.replicate (I.number v) true)
      (cons (List.replicate (J.number v) true) v)) := by
  simp only [applyNat₂,applyNat_bit,up_number]

structure PortListing (n : ℕ) where
  bound : Expr n
  valid : Expr (n+1)
  color : Expr (n+1)
  colorBound : Expr n
  incidence : Expr (n+2)

namespace PortListing

def eval (D : PortListing n) (v : Env n) : Descriptor.PortData where
  bound := D.bound.number v
  valid i := D.valid.bit (cons (List.replicate i true) v)
  color i := D.color.number (cons (List.replicate i true) v)
  colorBound := D.colorBound.number v
  incidence i j := D.incidence.bit (cons (List.replicate i true) (cons (List.replicate j true) v))

def up (D : PortListing n) : PortListing (n+1) where
  bound := D.bound.up
  valid := underOne D.valid
  color := underOne D.color
  colorBound := D.colorBound.up
  incidence := underTwo D.incidence

theorem eval_up (D : PortListing n) (v : Env n) (w : Word) : D.up.eval (cons w v)=D.eval v := by
  apply Descriptor.PortData.ext
  · rfl
  · funext i; exact underOne_bit D.valid v _ _
  · funext i; change ((underOne D.color).value _).length=_; rw [underOne_value]; rfl
  · rfl
  · funext i j; exact underTwo_bit D.incidence v _ _ _

def stride (D : PortListing n) : Expr n := add D.colorBound (numeral 2)
def owner (D : PortListing n) (I : Expr n) : Expr n := div (div I D.stride) (numeral 3)
def port (D : PortListing n) (I : Expr n) : Expr n := mod (div I D.stride) (numeral 3)
def level (D : PortListing n) (I : Expr n) : Expr n := mod I D.stride

theorem stride_number (D : PortListing n) (v : Env n) : D.stride.number v=(D.eval v).stride := by
  simp only [stride,add_number,numeral_number,Descriptor.PortData.stride,eval]

theorem owner_number (D : PortListing n) (I : Expr n) (v : Env n) :
    (D.owner I).number v=(D.eval v).owner (I.number v) := by
  simp only [owner,div_number,stride_number,numeral_number,Descriptor.PortData.owner]

theorem port_number (D : PortListing n) (I : Expr n) (v : Env n) :
    (D.port I).number v=(D.eval v).port (I.number v) := by
  simp only [port,mod_number,div_number,stride_number,numeral_number,Descriptor.PortData.port]

theorem level_number (D : PortListing n) (I : Expr n) (v : Env n) :
    (D.level I).number v=(D.eval v).level (I.number v) := by
  simp only [level,mod_number,stride_number,Descriptor.PortData.level]

def expandedValid (D : PortListing n) (I : Expr n) : Expr n :=
  conj (applyNat D.valid (D.owner I))
    (lt (D.level I) (add (applyNat D.color (D.owner I)) (numeral 2)))

def expandedEdge (D : PortListing n) (I J : Expr n) : Expr n :=
  disj (conj (eq (D.owner I) (D.owner J))
    (disj (conj (conj (eq (D.level I) (numeral 0)) (eq (D.level J) (numeral 0)))
        (neg (eq (D.port I) (D.port J))))
      (conj (eq (D.port I) (D.port J))
        (disj (eq (add (D.level I) (numeral 1)) (D.level J))
          (eq (add (D.level J) (numeral 1)) (D.level I))))))
    (conj (conj (eq (D.level I) (numeral 1)) (eq (D.level J) (numeral 1)))
      (applyNat₂ D.incidence (add (mul (numeral 3) (D.owner I)) (D.port I))
        (add (mul (numeral 3) (D.owner J)) (D.port J))))

theorem expandedValid_bit (D : PortListing n) (I : Expr n) (v : Env n) :
    (D.expandedValid I).bit v=(D.eval v).expanded.valid (I.number v) := by
  simp only [expandedValid,conj_bit,applyNat_bit,applyNat_number,lt_bit,add_number,
    numeral_number,owner_number,level_number]
  rfl

theorem expandedEdge_bit (D : PortListing n) (I J : Expr n) (v : Env n) :
    (D.expandedEdge I J).bit v=(D.eval v).expanded.edge (I.number v) (J.number v) := by
  simp only [expandedEdge,disj_bit,conj_bit,eq_bit,neg_bit,applyNat₂_bit,add_number,mul_number,
    numeral_number,owner_number,port_number,level_number]
  have hd : (!(decide ((D.eval v).port (I.number v)=(D.eval v).port (J.number v)))) =
      decide ((D.eval v).port (I.number v)≠(D.eval v).port (J.number v)) := decide_not.symm
  rw [hd]
  rfl

def expanded (D : PortListing n) : GraphListing n where
  bound := mul (mul (numeral 3) D.bound) D.stride
  valid := D.up.expandedValid (input 0)
  edge := D.up.up.expandedEdge (input 0) (input 1)

theorem expanded_eval (D : PortListing n) (v : Env n) :
    D.expanded.eval v=(D.eval v).expanded := by
  apply Descriptor.data_ext
  · simp only [expanded,GraphListing.eval,mul_number,numeral_number,stride_number,Descriptor.PortData.expanded,eval]
  · funext i
    simp only [expanded,GraphListing.eval,expandedValid_bit,input_number,cons_zero,List.length_replicate,eval_up]
  · funext i j
    simp only [expanded,GraphListing.eval,expandedEdge_bit,input_number,cons_zero,NumericProgram.cons_one,
      List.length_replicate,eval_up]

end PortListing
end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

def fixedNat : (N : ℕ) → (Fin N → ℕ) → Expr n → Expr n
  | 0,_,_ => numeral 0
  | N+1,f,I => choose (eq I (numeral 0)) (numeral (f 0))
      (fixedNat N (fun i=>f i.succ) (sub I (numeral 1)))

theorem fixedNat_number (N : ℕ) (f : Fin N → ℕ) (I : Expr n) (v : Env n)
    (h : I.number v<N) : (fixedNat N f I).number v=f ⟨I.number v,h⟩ := by
  induction N generalizing I with
  | zero => omega
  | succ N ih =>
    rw [fixedNat,NumericProgram.choose_number,eq_bit,numeral_number]
    by_cases hi : I.number v=0
    · rw [ite_eq_left (by simpa using hi),numeral_number]
      exact congrArg f (Fin.ext hi.symm)
    · rw [ite_eq_right (by simpa using hi),ih (fun i=>f i.succ) _ (by simp only [sub_number,numeral_number]; omega)]
      apply congrArg f
      apply Fin.ext
      simp only [Fin.val_succ,sub_number,numeral_number]
      omega

def fixedBool (N : ℕ) (f : Fin N → Bool) (I : Expr n) : Expr n :=
  eq (fixedNat N (fun i=>if f i then 1 else 0) I) (numeral 1)

theorem fixedBool_bit (N : ℕ) (f : Fin N → Bool) (I : Expr n) (v : Env n)
    (h : I.number v<N) : (fixedBool N f I).bit v=f ⟨I.number v,h⟩ := by
  simp only [fixedBool,eq_bit,fixedNat_number N _ I v h,numeral_number]
  cases f ⟨I.number v,h⟩ <;> rfl

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Computation.Stack.Recipe
@[simp] theorem cons_two {n : ℕ} (a b c : Word) (v : Env n) : cons a (cons b (cons c v)) (2 : Fin (n+3))=c := rfl
end VariableWL.Computation.Stack.Recipe

end OAI
