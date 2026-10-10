import Mathlib
import OAI.Computability.MinUncut.Estimates.HeapInitializationMath

namespace OAI

noncomputable section
namespace MinUncut.Costed.FiberPrefix
open Turing.ToPartrec Polynomial
lemma scalar_code {f : ℕ → ℕ} (hf : Computable f) :
    ∃c : Code,∀K,[f K]∈c.eval [K] := by
  obtain ⟨c,hc⟩:=Code.exists_code (Nat.Partrec'.part_iff₁.mpr hf)
  refine ⟨c,fun K=>?_⟩
  have h:=hc ⟨[K],rfl⟩
  rw [h]
  change [f K]∈Part.some [f K]
  exact Part.mem_some _
lemma scalar₂_code {f : ℕ → ℕ → ℕ} (hf : Computable₂ f) :
    ∃c : Code,∀K i,[f K i]∈c.eval [K,i] := by
  obtain ⟨c,hc⟩:=Code.exists_code (Nat.Partrec'.part_iff₂.mpr hf.partrec₂)
  refine ⟨c,fun K i=>?_⟩
  have h:=hc ⟨[K,i],rfl⟩
  rw [h]
  change [f K i]∈Part.some [f K i]
  exact Part.mem_some _

def args : Code := .cons (.comp .head .tail) .head
lemma run_args (i K : ℕ) (rest : List ℕ) :
    Runs args (i::K::rest) [K,i] (2000*(magnitude (i::K::rest)+1)) := by
  have h:=run_cons (run_comp (run_tail (i::K::rest)) (run_head (K::rest))) (run_head (i::K::rest))
  apply h.mono
  simp only [magnitude_cons,magnitude_nil,List.headI_cons]
  omega

def step (cell : Code) : Code :=
  .cons .succ (.cons (.comp .head .tail) (.cons (.comp cell args) (.comp .tail .tail)))
lemma run_step (cell : Code) (i K z C : ℕ) (rest : List ℕ)
    (hc : Runs cell [K,i] [z] C) :
    Runs (step cell) (i::K::rest) ((i+1)::K::z::rest)
      (C+10000*(magnitude (i::K::rest)+z+1)) := by
  have hp:=run_comp (run_args i K rest) hc
  have ht:=run_comp (run_tail (i::K::rest)) (run_tail (K::rest))
  have hk:=run_comp (run_tail (i::K::rest)) (run_head (K::rest))
  have hh:=run_cons (run_succ (i::K::rest)) (run_cons hk (run_cons hp ht))
  apply hh.mono
  simp only [magnitude_cons,magnitude_nil,List.headI_cons]
  omega

def state (f : ℕ → List ℕ) (K i : ℕ) (v : List ℕ) : List ℕ :=
  i::K::((f K).reverse.take i).reverse++v
lemma state_zero (f : ℕ → List ℕ) (K : ℕ) (v : List ℕ) : state f K 0 v=0::K::v := rfl
lemma state_step (f : ℕ → List ℕ) (K i : ℕ) (v : List ℕ) (hi : i<(f K).length) :
    state f K (i+1) v=(i+1)::K::((f K).reverse[i]?.getD 0)::((f K).reverse.take i).reverse++v := by
  have hlen:i<(f K).reverse.length:=by simpa using hi
  simp only [state,List.take_succ_eq_append_getElem hlen,List.reverse_append,List.reverse_singleton,
    List.singleton_append,List.getElem?_eq_getElem hlen,Option.getD_some]
lemma magnitude_append (v w : List ℕ) : magnitude (v++w)=magnitude v+magnitude w := by
  induction v with
  | nil => simp only [List.nil_append,magnitude_nil,Nat.zero_add]
  | cons a v ih => simp only [List.cons_append,magnitude_cons,ih]; omega
lemma magnitude_reverse (v : List ℕ) : magnitude v.reverse=magnitude v := by
  induction v with
  | nil => rfl
  | cons a v ih => simp only [List.reverse_cons,magnitude_append,magnitude_cons,magnitude_nil,ih]; omega
lemma magnitude_take (i : ℕ) (v : List ℕ) : magnitude (v.take i)≤ magnitude v := by
  induction i generalizing v with
  | zero => simp [magnitude]
  | succ i ih => cases v with
    | nil => rfl
    | cons a v => simpa only [List.take_succ_cons,magnitude_cons] using Nat.add_le_add_left (ih v) (a+1)
lemma state_size (f : ℕ → List ℕ) (K i : ℕ) (v : List ℕ) :
    magnitude (state f K i v)≤ i + K + 2 + magnitude (f K) + magnitude v := by
  have ht:=magnitude_take i (f K).reverse
  simp only [state,List.cons_append,magnitude_cons,magnitude_append,magnitude_reverse] at *
  omega

def init (len : Code) : Code :=
  .cons (.comp len .head) (.cons .zero (.cons .head .id))
lemma run_init (len : Code) (K n C : ℕ) (v : List ℕ)
    (hc : Runs len [K] [n] C) :
    Runs (init len) (K::v) (n::0::K::K::v)
      (C+3000*(magnitude (K::v)+n+1)) := by
  have h:=run_cons (run_comp (run_head (K::v)) hc)
    (run_cons (run_const_zero (K::v)) (run_cons (run_head (K::v)) (run_id (K::v))))
  apply h.mono
  simp only [magnitude_cons,magnitude_nil,List.headI_cons]
  omega

def code (len cell : Code) : Code :=
  .comp (.comp .tail .tail) (.comp (iterCode (step cell)) (init len))
def transition (f : ℕ → List ℕ) (v : List ℕ) : List ℕ :=
  (v.headI+1)::(v.tail.headI)::((f v.tail.headI).reverse[v.headI]?.getD 0)::v.drop 2
lemma iterate_state (f : ℕ → List ℕ) (K i : ℕ) (v : List ℕ) (hi : i≤(f K).length) :
    (transition f)^[i] (0::K::v)=state f K i v := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply',ih (by omega),state_step f K i v (by omega)]
    rfl
lemma run_code {f : ℕ → List ℕ} {len cell : Code}
    (hlen : ∀K,[((f K).length)]∈len.eval [K])
    (hcell : ∀K i,[(f K).reverse[i]?.getD 0]∈cell.eval [K,i]) (K : ℕ) :
    ∃p : Polynomial ℕ,∀v,Runs (code len cell) (K::v) (f K++K::v)
      (p.eval (magnitude (K::v))) ∧
      magnitude (f K++K::v)≤p.eval (magnitude (K::v)) := by
  obtain ⟨A,hA⟩:=CodeRun.complete (hlen K)
  have ht:∀i,∃T,CodeRun cell [K,i] [(f K).reverse[i]?.getD 0] T :=
    fun i=>CodeRun.complete (hcell K i)
  let n:=(f K).length
  let C:=((Finset.range (n+1)).sum (fun i=>Classical.choose (ht i)+(f K).reverse[i]?.getD 0))
  have hc (i : ℕ) (hi : i≤n) :
      Runs cell [K,i] [(f K).reverse[i]?.getD 0] C ∧ (f K).reverse[i]?.getD 0≤C := by
    have hs:=Finset.single_le_sum (f:=fun i=>Classical.choose (ht i)+(f K).reverse[i]?.getD 0)
      (fun j _=>Nat.zero_le _) (show i∈Finset.range (n+1) by simp; omega)
    exact ⟨⟨_,by dsimp [C]; omega,Classical.choose_spec (ht i)⟩,by dsimp [C]; omega⟩
  let q : Polynomial ℕ := X+Polynomial.C (n+K+2+magnitude (f K))
  let b : Polynomial ℕ := Polynomial.C C+Polynomial.C 10000*(q+Polynomial.C C+1)
  let p : Polynomial ℕ := Polynomial.C A+Polynomial.C 3000*(X+Polynomial.C n+1)+
    Polynomial.C (n+1)*(b+Polynomial.C 5000*(Polynomial.C n+q+4))+
    Polynomial.C 100*(q+1)+Polynomial.C (magnitude (f K))+X+2
  refine ⟨p,fun v=>?_⟩
  have hs (i : ℕ) (hi : i≤n) : magnitude ((transition f)^[i] (0::K::K::v))≤q.eval (magnitude (K::v)) := by
    rw [iterate_state f K i (K::v) hi]
    have hh:=state_size f K i (K::v)
    simp only [q,eval_add,eval_X,eval_C]
    omega
  have hh:=run_iter (c:=step cell) (transition f) n (0::K::K::v)
    (q.eval (magnitude (K::v))) (b.eval (magnitude (K::v))) hs (by
      intro i hi
      rw [iterate_state f K i (K::v) (by omega),iterate_state f K (i+1) (K::v) (by omega)]
      rw [state_step f K i (K::v) hi]
      have hr:=run_step cell i K ((f K).reverse[i]?.getD 0) C
        (((f K).reverse.take i).reverse++K::v) (hc i (by omega)).1
      apply hr.mono
      have hsize:=hs i (by omega)
      rw [iterate_state f K i (K::v) (by omega)] at hsize
      have hz:=(hc i (by omega)).2
      simp only [b,eval_add,eval_mul,eval_C,eval_one]
      change C+10000*(magnitude (state f K i (K::v))+_+1)≤_
      omega)
  have hend : (transition f)^[n] (0::K::K::v)=n::K::(f K++K::v) := by
    rw [iterate_state f K n (K::v) le_rfl]
    simp only [state,n,List.cons_append]
    rw [show (f K).length=(f K).reverse.length from List.length_reverse.symm,
      List.take_length,List.reverse_reverse]
  rw [hend] at hh
  have hinit:=run_init len K n A v ⟨A,le_rfl,hA⟩
  have htail:=run_comp (run_tail (n::K::(f K++K::v))) (run_tail (K::(f K++K::v)))
  have hr:=run_comp (run_comp hinit hh) htail
  constructor
  · apply hr.mono
    have hlast:=hs n le_rfl
    rw [hend] at hlast
    simp only [p,eval_add,eval_mul,eval_C,eval_X,eval_one,eval_ofNat]
    simp only [magnitude_cons] at hlast ⊢
    omega
  · simp only [p,eval_add,eval_mul,eval_C,eval_X,eval_one,eval_ofNat,magnitude_append]
    omega

lemma exists_code {f : ℕ → List ℕ} (hf : Computable f) :
    ∃c : Code,∀K,∃p : Polynomial ℕ,∀v,
      Runs c (K::v) (f K++K::v) (p.eval (magnitude (K::v))) ∧
      magnitude (f K++K::v)≤p.eval (magnitude (K::v)) := by
  have hl:Computable (fun K=>(f K).length) := Primrec.list_length.to_comp.comp hf
  have hg:Computable₂ (fun K i=>(f K).reverse[i]?.getD 0) :=
    Primrec.option_getD.to_comp.comp
      (Primrec.list_getElem?.to_comp.comp (Primrec.list_reverse.to_comp.comp (hf.comp Computable.fst)) Computable.snd)
      (Computable.const 0)
  obtain ⟨l,hl⟩:=scalar_code hl
  obtain ⟨g,hg⟩:=scalar₂_code hg
  exact ⟨code l g,run_code hl hg⟩
end MinUncut.Costed.FiberPrefix

end
namespace MinUncut.Costed.Arena

lemma listCells_ptr' (v : List ℕ) (h : Heap) :
    (listCells v h).1=if v=[] then 0 else v.length+h.length := by
  cases v with
  | nil => rfl
  | cons a v => simp only [listCells,listCells_length,List.cons_ne_nil,ite_false,List.length_cons]; omega

lemma listCells_get (v : List ℕ) (h : Heap) (i : ℕ) (hi : i<v.length) :
    (listCells v h).2[i]'(by rw [listCells_length]; omega)=
      node v[i] (if i+1=v.length then 0 else h.length+v.length-i-1) 0 0 := by
  induction v generalizing i with
  | nil => simp at hi
  | cons a v ih =>
    cases i with
    | zero =>
      simp only [listCells,List.getElem_cons_zero,listCells_ptr',List.length_cons,
        Nat.zero_add,Nat.sub_zero]
      by_cases hv : v=[]
      · simp [hv]
      · have hl : v.length≠0 := fun hz=>hv (List.length_eq_zero_iff.mp hz)
        simp only [hv,ite_false,show ¬1=v.length+1 by omega,ite_false]
        congr 1
        omega
    | succ i =>
      simp only [listCells,List.getElem_cons_succ]
      rw [ih i (by simpa using hi)]
      congr 1
      simp only [List.length_cons]
      split_ifs <;> omega

lemma listCells_drop (v : List ℕ) (h : Heap) : (listCells v h).2.drop v.length=h := by
  induction v with
  | nil => rfl
  | cons a v ih => simpa only [listCells,List.length_cons,List.drop_succ_cons] using ih

def dataCells (v : List ℕ) (b : ℕ) : Heap :=
  (List.range v.length).map (fun i=> node ((v.drop i).headI)
    (if i+1=v.length then 0 else b+v.length-i-1) 0 0)
lemma dataCells_length (v : List ℕ) (b : ℕ) : (dataCells v b).length=v.length := by simp [dataCells]
lemma dataCells_eq_take (v : List ℕ) (h : Heap) :
    dataCells v h.length=(listCells v h).2.take v.length := by
  apply List.ext_getElem
  · simp only [dataCells_length,List.length_take,listCells_length]; omega
  · intro i hi ht
    have hiv : i<v.length := by simpa only [dataCells_length] using hi
    simp only [dataCells,List.getElem_map,List.getElem_range,List.getElem_take]
    rw [listCells_get v h i hiv,List.drop_eq_getElem_cons hiv]
    rfl
lemma listCells_split (v : List ℕ) (h : Heap) :
    (listCells v h).2=dataCells v h.length++h := by
  rw [dataCells_eq_take]
  calc
    _ = (listCells v h).2.take v.length++(listCells v h).2.drop v.length := (List.take_append_drop _ _).symm
    _ = _ := by rw [listCells_drop]
end MinUncut.Costed.Arena

namespace MinUncut.Costed
open Polynomial

def quadruple (v : List ℕ) : List ℕ := v.reverse++v++v.reverse++v
lemma quadruple_length (v : List ℕ) : (quadruple v).length=4*v.length := by
  simp only [quadruple,List.length_append,List.length_reverse]; omega

def quadrupleWords (v : List ℕ) : List ℕ :=
  (prefixStep^[2*v.headI] (0::(prefixStep^[v.headI] (0::v.tail)).tail)).tail
noncomputable def quadrupleProgram : PolyProgram quadrupleWords :=
  reversePrefixProgram.comp (((AExpr.mul (.const 2) (.reg 0)).program).cons reversePrefixProgram)
lemma quadruple_spec (v : List ℕ) : quadrupleWords (v.length::v)=quadruple v := by
  have hr := reversePrefix_spec v []
  simp only [List.append_nil] at hr
  simp only [quadrupleWords,List.headI_cons,List.tail_cons,hr]
  have hs := reversePrefix_spec (v.reverse++v) []
  simp only [List.append_nil,List.length_append,List.length_reverse] at hs
  rw [show 2*v.length=v.length+v.length by omega,hs]
  simp only [List.reverse_append,List.reverse_reverse,quadruple,List.append_assoc]
end MinUncut.Costed

namespace MinUncut.Costed.Arena.Init
open Turing.ToPartrec

def input (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) : List ℕ :=
  (codeCells c 0).length::(words (codeCells c 0)++K::rest.length::xs.length::(xs.reverse++rest))

def countExpr : AExpr := .reg 0
def sizeExpr : AExpr := .at (.add (.mul (.const 4) countExpr) (.const 3))
def restExpr : AExpr := .at (.add (.mul (.const 4) countExpr) (.const 2))
def lengthExpr : AExpr := .add (.add (.add (.mul (.const 4) countExpr) (.const 4)) sizeExpr) restExpr

lemma input_drop (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    (input c xs K rest).drop (4*(codeCells c 0).length+1)=K::rest.length::xs.length::(xs.reverse++rest) := by
  simp only [input,List.drop_succ_cons]
  rw [←length_words,List.drop_left]
lemma input_count (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    countExpr.eval (input c xs K rest)=(codeCells c 0).length := rfl
lemma input_size (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    sizeExpr.eval (input c xs K rest)=xs.length := by
  simp only [sizeExpr,AExpr.eval,input_count]
  rw [show 4*(codeCells c 0).length+3=(4*(codeCells c 0).length+1)+2 by omega,
    ←List.drop_drop,input_drop]
  rfl
lemma input_rest (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    restExpr.eval (input c xs K rest)=rest.length := by
  simp only [restExpr,AExpr.eval,input_count]
  rw [show 4*(codeCells c 0).length+2=(4*(codeCells c 0).length+1)+1 by omega,
    ←List.drop_drop,input_drop]
  rfl
lemma input_length (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    (input c xs K rest).length=4*(codeCells c 0).length+4+xs.length+rest.length := by
  simp only [input,List.length_cons,List.length_append,length_words,List.length_reverse]; omega
lemma input_lengthExpr (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    lengthExpr.eval (input c xs K rest)=(input c xs K rest).length := by
  simp only [lengthExpr,AExpr.eval,input_count,input_size,input_rest,input_length]

def canvas (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) : List ℕ :=
  [(codeCells c 0).length,xs.length,(input c xs K rest).length,0]++quadruple (input c xs K rest)
def canvasWords (v : List ℕ) : List ℕ :=
  [countExpr.eval v,sizeExpr.eval v,lengthExpr.eval v,0]++quadrupleWords (lengthExpr.eval v::v)
noncomputable def canvasProgram : PolyProgram canvasWords :=
  PolyProgram.expressions (quadrupleProgram.comp (lengthExpr.program.cons PolyProgram.id))
    [countExpr,sizeExpr,lengthExpr,.const 0]
lemma canvasProgram_spec (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    canvasWords (input c xs K rest)=canvas c xs K rest := by
  simp only [canvasWords,input_count,input_size,input_lengthExpr,quadruple_spec,canvas]
lemma canvas_length (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    (canvas c xs K rest).length=4*((input c xs K rest).length+1) := by
  simp only [canvas,List.length_append,List.length_cons,List.length_nil,quadruple_length]; omega
lemma canvas_drop (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    (canvas c xs K rest).drop (4+(input c xs K rest).length)=
      input c xs K rest++(input c xs K rest).reverse++input c xs K rest := by
  simp only [canvas,quadruple]
  rw [←List.drop_drop]
  simp only [List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero]
  rw [List.append_assoc,List.append_assoc,show (input c xs K rest).length=(input c xs K rest).reverse.length from List.length_reverse.symm,List.drop_left]
  simp only [List.append_assoc]
lemma canvas_at (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ)
    (i : ℕ) (hi : i<(input c xs K rest).length) :
    ((canvas c xs K rest).drop (4+(input c xs K rest).length+i)).headI=
      ((input c xs K rest).drop i).headI := by
  rw [←List.drop_drop,canvas_drop]
  rw [List.append_assoc,List.drop_append_of_le_length hi.le,List.drop_eq_getElem_cons hi]
  rfl

open Turing.ToPartrec

def cExpr : AExpr := .reg 1
def mExpr : AExpr := .reg 2
def lExpr : AExpr := .reg 3
def iExpr : AExpr := .reg 0
def bExpr : AExpr := .add (.add (.add cExpr mExpr) lExpr) (.const 1)
def rawCell (j : ℕ) : AExpr :=
  .at (.add (.add (.add lExpr (.const 6)) (.mul (.const 4) (.sub iExpr mExpr))) (.const j))
def rawData : AExpr :=
  .at (.add (.add (.add lExpr (.mul (.const 4) cExpr)) (.const 9)) (.sub (.sub mExpr (.const 1)) iExpr))
def pointerExpr (a : AExpr) : AExpr := .cond (.eq a (.const 0)) (.add bExpr a) (.const 0)
def isData : AExpr := .le (.add iExpr (.const 1)) mExpr
def dataPointer : AExpr := .cond (.eq (.add iExpr (.const 1)) mExpr)
  (.sub (.sub (.add (.add bExpr cExpr) mExpr) iExpr) (.const 1)) (.const 0)
def rowExpressions : List AExpr :=
  [.cond isData (rawCell 0) rawData,.cond isData (pointerExpr (rawCell 1)) dataPointer,
   .cond isData (pointerExpr (rawCell 2)) (.const 0),.cond isData (rawCell 3) (.const 0)]

def baseLength (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) : ℕ :=
  (codeCells c 0).length+xs.length+(input c xs K rest).length+1
lemma cExpr_eval (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) (i : ℕ) :
    cExpr.eval (i::canvas c xs K rest)=(codeCells c 0).length := rfl
lemma mExpr_eval (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) (i : ℕ) :
    mExpr.eval (i::canvas c xs K rest)=xs.length := rfl
lemma lExpr_eval (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) (i : ℕ) :
    lExpr.eval (i::canvas c xs K rest)=(input c xs K rest).length := rfl
lemma iExpr_eval (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) (i : ℕ) :
    iExpr.eval (i::canvas c xs K rest)=i := rfl
lemma bExpr_eval (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) (i : ℕ) :
    bExpr.eval (i::canvas c xs K rest)=baseLength c xs K rest := rfl

lemma at_append (v w : List ℕ) (i : ℕ) (hi : i<v.length) :
    ((v++w).drop i).headI=(v.drop i).headI := by
  rw [List.drop_append_of_le_length hi.le,List.drop_eq_getElem_cons hi]
  rfl

lemma rawCell_eval (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ)
    (i : ℕ) (hi : i-xs.length<(codeCells c 0).length) (j : Fin 4) :
    (rawCell j.val).eval (i::canvas c xs K rest)=
      (((codeCells c 0).drop (i-xs.length)).headD (fun _=>0)) j := by
  simp only [rawCell,AExpr.eval,lExpr_eval,iExpr_eval,mExpr_eval]
  rw [show (input c xs K rest).length+6+4*(i-xs.length)+j.val=
    (4+(input c xs K rest).length+(1+4*(i-xs.length)+j.val))+1 by omega,List.drop_succ_cons]
  rw [canvas_at c xs K rest _ (by rw [input_length]; omega)]
  rw [show 1+4*(i-xs.length)+j.val=(4*(i-xs.length)+j.val)+1 by omega]
  simp only [input,List.drop_succ_cons]
  rw [at_append _ _ _ (by rw [length_words]; omega),words_at]

lemma rawData_eval (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ)
    (i : ℕ) (hi : i<xs.length) :
    rawData.eval (i::canvas c xs K rest)=xs[i] := by
  simp only [rawData,AExpr.eval,lExpr_eval,iExpr_eval,mExpr_eval,cExpr_eval]
  rw [show (input c xs K rest).length+4*(codeCells c 0).length+9+(xs.length-1-i)=
    (4+(input c xs K rest).length+(4*(codeCells c 0).length+4+(xs.length-1-i)))+1 by omega,List.drop_succ_cons]
  rw [canvas_at c xs K rest _ (by rw [input_length]; omega)]
  rw [show 4*(codeCells c 0).length+4+(xs.length-1-i)=
    (4*(codeCells c 0).length+1)+(3+(xs.length-1-i)) by omega,←List.drop_drop,input_drop]
  simp only [show 3+(xs.length-1-i)=(xs.length-1-i)+3 by omega,
    List.drop_succ_cons]
  have hr : xs.length-1-i<xs.reverse.length := by simp only [List.length_reverse]; omega
  rw [at_append _ _ _ hr,List.drop_eq_getElem_cons hr]
  simp only [List.headI_cons,List.getElem_reverse]
  congr 1
  omega

lemma pointerExpr_eval (a : AExpr) (v : List ℕ) :
    (pointerExpr a).eval v=rebasePointer (bExpr.eval v) (a.eval v) := by
  simp only [pointerExpr,AExpr.eval,rebasePointer]
  by_cases h : a.eval v=0 <;> simp only [h,ite_true,ite_false,Nat.one_ne_zero]

lemma row_data (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ)
    (i : ℕ) (hi : i<xs.length) :
    Blocks.block rowExpressions i (canvas c xs K rest)=
      [xs[i],if i+1=xs.length then 0 else baseLength c xs K rest+(codeCells c 0).length+xs.length-i-1,0,0] := by
  have hdata : isData.eval (i::canvas c xs K rest)=1 := by
    simp only [isData,AExpr.eval,iExpr_eval,mExpr_eval]
    exact ite_eq_left (by omega)
  have hp : dataPointer.eval (i::canvas c xs K rest)=
      if i+1=xs.length then 0 else baseLength c xs K rest+(codeCells c 0).length+xs.length-i-1 := by
    unfold dataPointer
    by_cases h : i+1=xs.length <;>
      simp only [AExpr.eval,iExpr_eval,mExpr_eval,cExpr_eval,bExpr_eval,h,ite_true,ite_false,Nat.one_ne_zero]
  simp only [Blocks.block,rowExpressions,List.map_cons,List.map_nil,AExpr.eval,hdata,
    Nat.one_ne_zero,ite_false,rawData_eval c xs K rest i hi,hp]
lemma row_code (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ)
    (i : ℕ) (hm : xs.length ≤ i) (hi : i-xs.length<(codeCells c 0).length) :
    Blocks.block rowExpressions i (canvas c xs K rest)=
      List.ofFn (rebaseNode (baseLength c xs K rest)
        (((codeCells c 0).drop (i-xs.length)).headD (fun _=>0))) := by
  have hd : isData.eval (i::canvas c xs K rest)=0 := by
    simp only [isData,AExpr.eval,iExpr_eval,mExpr_eval]
    exact ite_eq_right (by omega)
  have h0 := rawCell_eval c xs K rest i hi (0:Fin 4)
  have h1 := rawCell_eval c xs K rest i hi (1:Fin 4)
  have h2 := rawCell_eval c xs K rest i hi (2:Fin 4)
  have h3 := rawCell_eval c xs K rest i hi (3:Fin 4)
  change (rawCell 0).eval (i::canvas c xs K rest)=_ at h0
  change (rawCell 1).eval (i::canvas c xs K rest)=_ at h1
  change (rawCell 2).eval (i::canvas c xs K rest)=_ at h2
  change (rawCell 3).eval (i::canvas c xs K rest)=_ at h3
  simp only [Blocks.block,rowExpressions,List.map_cons,List.map_nil,AExpr.eval,hd,ite_true,
    pointerExpr_eval,h0,h1,h2,h3,bExpr_eval]
  rfl

open Turing.ToPartrec

def newHeap (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) : Heap :=
  dataCells xs (baseLength c xs K rest+(codeCells c 0).length)++
    codeCells c (baseLength c xs K rest)

def countRows : AExpr := .add (.reg 0) (.reg 1)
lemma countRows_eval (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    countRows.eval (canvas c xs K rest)=(codeCells c 0).length+xs.length := rfl

lemma map_drop_head (h : Heap) :
    (List.range h.length).map (fun i=>(h.drop i).headD (fun _=>0))=h := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range]
    rw [List.drop_eq_getElem_cons hj]
    rfl

lemma emitted_data (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    (List.range xs.length).flatMap (fun i=>Blocks.block rowExpressions i (canvas c xs K rest))=
      words (dataCells xs (baseLength c xs K rest+(codeCells c 0).length)) := by
  simp only [words,dataCells,List.flatMap_map]
  apply List.flatMap_congr
  intro i hi
  have hi' : i<xs.length := List.mem_range.mp hi
  rw [row_data c xs K rest i hi',List.drop_eq_getElem_cons hi']
  rfl

lemma emitted_code (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    (List.range (codeCells c 0).length).flatMap
      (fun i=>Blocks.block rowExpressions (xs.length+i) (canvas c xs K rest))=
      words (codeCells c (baseLength c xs K rest)) := by
  have he := codeCells_rebase c 0 (baseLength c xs K rest)
  simp only [Nat.zero_add] at he
  conv_rhs => rw [he,←map_drop_head (codeCells c 0)]
  simp only [words,List.map_map,List.flatMap_map,Function.comp_def]
  apply List.flatMap_congr
  intro i hi
  have hi' : i<(codeCells c 0).length := List.mem_range.mp hi
  convert row_code c xs K rest (xs.length+i) (by omega) (by omega) using 1
  simp only [Nat.add_sub_cancel_left]

lemma emitted_spec (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    Blocks.emitted rowExpressions (countRows.eval (canvas c xs K rest)) (canvas c xs K rest)=
      words (newHeap c xs K rest) := by
  rw [countRows_eval,show (codeCells c 0).length+xs.length=xs.length+(codeCells c 0).length by omega]
  simp only [Blocks.emitted,List.range_add,List.flatMap_append,List.flatMap_map]
  rw [emitted_data,emitted_code,newHeap,words_append]

lemma newHeap_length (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    (newHeap c xs K rest).length=(codeCells c 0).length+xs.length := by
  simp only [newHeap,List.length_append,dataCells_length,codeCells_length_eq c (baseLength c xs K rest) 0]
  omega

open Turing.ToPartrec

def oldWords (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) : List ℕ :=
  Blocks.retained rowExpressions (countRows.eval (canvas c xs K rest)) (canvas c xs K rest)
def base (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) : Heap :=
  groupWords (oldWords c xs K rest)
lemma oldWords_length (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    (oldWords c xs K rest).length=4*baseLength c xs K rest := by
  simp only [oldWords,Blocks.retained,List.length_append,List.length_reverse,emitted_spec,
    length_words,newHeap_length,canvas_length,baseLength]
  omega
lemma base_length (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    (base c xs K rest).length=baseLength c xs K rest := by
  rw [base,groupWords_length,oldWords_length]
  omega
lemma base_words (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    words (base c xs K rest)=oldWords c xs K rest := by
  exact groupWords_words _ (by rw [oldWords_length]; exact dvd_mul_right _ _)
lemma heap_match (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    (initialState c xs (base c xs K rest)).heap=newHeap c xs K rest++base c xs K rest := by
  simp only [initialState,listCells_split,List.length_append,base_length,
    codeCells_length_eq c (baseLength c xs K rest) 0,newHeap,List.append_assoc]
  rw [Nat.add_comm (codeCells c 0).length (baseLength c xs K rest)]

def canvasBase : AExpr := .add (.add countRows (.reg 2)) (.const 1)
def canvasPc : AExpr := .add canvasBase (.reg 0)
def canvasTotal : AExpr := .add canvasBase countRows
def canvasEnv : AExpr := .cond (.eq (.reg 1) (.const 0)) canvasTotal (.const 0)
def header : List AExpr := [.const 0,canvasPc,canvasEnv,.const 0,canvasTotal]
lemma canvasBase_eval (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    canvasBase.eval (canvas c xs K rest)=baseLength c xs K rest := rfl
lemma canvasPc_eval (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    canvasPc.eval (canvas c xs K rest)=baseLength c xs K rest+(codeCells c 0).length := rfl
lemma canvasTotal_eval (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    canvasTotal.eval (canvas c xs K rest)=baseLength c xs K rest+((codeCells c 0).length+xs.length) := rfl
lemma canvasEnv_eval (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    canvasEnv.eval (canvas c xs K rest)=
      if xs=[] then 0 else baseLength c xs K rest+((codeCells c 0).length+xs.length) := by
  change (if (if xs.length=0 then 1 else 0)=0 then canvasTotal.eval (canvas c xs K rest) else 0)=_
  by_cases h : xs=[]
  · simp only [h,List.length_nil,ite_true,Nat.one_ne_zero,ite_false]
  · have hl : xs.length≠0 := fun hh=>h (List.length_eq_zero_iff.mp hh)
    simp only [hl,ite_false,ite_true,canvasTotal_eval,h]
lemma header_match (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    header.map (fun a=>a.eval (canvas c xs K rest))=
      [0,(initialState c xs (base c xs K rest)).pc,
        (initialState c xs (base c xs K rest)).env,0,
        (initialState c xs (base c xs K rest)).heap.length] := by
  simp only [header,List.map_cons,List.map_nil,AExpr.eval,canvasPc_eval,canvasEnv_eval,canvasTotal_eval]
  simp only [initialState,listCells_ptr,listCells_length,List.length_append,base_length,
    codeCells_length_eq c (baseLength c xs K rest) 0]
  simp only [Nat.add_comm,Nat.add_left_comm]

def initialized (v : List ℕ) : List ℕ :=
  (header.map (fun a=>a.eval (canvasWords v)))++
    (Blocks.emitted rowExpressions (countRows.eval (canvasWords v)) (canvasWords v)++
      Blocks.retained rowExpressions (countRows.eval (canvasWords v)) (canvasWords v))
noncomputable def initializer : PolyProgram initialized :=
  ((PolyProgram.expressions (Blocks.forward rowExpressions countRows) header).comp canvasProgram).ofEq (by intro v; rfl)
lemma initializer_spec (c : Code) (xs : List ℕ) (K : ℕ) (rest : List ℕ) :
    initialized (input c xs K rest)=(initialState c xs (base c xs K rest)).encode := by
  simp only [initialized,canvasProgram_spec,header_match,emitted_spec]
  rw [State.encode]
  have hz : (initialState c xs (base c xs K rest)).mode=0 := rfl
  have hk : (initialState c xs (base c xs K rest)).kont=0 := rfl
  rw [hz,hk,heap_match,words_append,base_words]
  rfl

end MinUncut.Costed.Arena.Init

namespace MinUncut.Costed.UnaryWords
open Turing.ToPartrec Polynomial Arena

def symbol (v : List ℕ) : ℕ := (v.drop (3+(v.drop 2).headI+v.headI)).headI

def step (v : List ℕ) : List ℕ :=
  if symbol v=1 then
    (v.headI+1)::0::((v.drop 2).headI+1)::(v.drop 1).headI::v.drop 3
  else (v.headI+1)::((v.drop 1).headI+1)::(v.drop 2).headI::v.drop 3

def finish (v : List ℕ) : List ℕ := (v.drop 2).headI::v.drop 3

def body (v : List ℕ) : List ℕ := if symbol v=0 then 0::finish v else 1::step v

noncomputable def symbolProgram : PolyProgram (fun v=>[symbol v]) :=
  (AExpr.at (.add (.add (.const 3) (.reg 2)) (.reg 0))).program
noncomputable def stepProgram : PolyProgram step :=
  (PolyProgram.branch (PolyProgram.eqOf symbolProgram (PolyProgram.const 1))
    (PolyProgram.succ.cons (((AExpr.add (.reg 1) (.const 1)).program).cons
      ((PolyProgram.projection 2).cons (PolyProgram.drop 3))))
    (PolyProgram.succ.cons ((PolyProgram.const 0).cons
      (((AExpr.add (.reg 2) (.const 1)).program).cons
        ((PolyProgram.projection 1).cons (PolyProgram.drop 3)))))).ofEq (by
      intro v
      simp only [step,AExpr.eval,List.headI_cons]
      by_cases h : symbol v=1 <;> simp only [h,ite_true,ite_false,Nat.one_ne_zero])
noncomputable def finishProgram : PolyProgram finish :=
  (PolyProgram.projection 2).cons (PolyProgram.drop 3)
noncomputable def bodyProgram : PolyProgram body :=
  (PolyProgram.branch symbolProgram (PolyProgram.zero.comp finishProgram)
    ((PolyProgram.const 1).cons stepProgram)).ofEq (by intro v; rfl)

lemma step_safe (v : List ℕ) :
    (step v).length≤v.length+4 ∧ maximum (step v)≤ maximum v+1 := by
  have h0:=head_le_maximum v
  have h1:=(head_le_maximum (v.drop 1)).trans (maximum_drop v 1)
  have h2:=(head_le_maximum (v.drop 2)).trans (maximum_drop v 2)
  have h3:=maximum_drop v 3
  have hl:=(show (v.drop 3).length ≤ v.length from by simp only [List.length_drop]; omega)
  unfold step
  split_ifs <;> simp only [List.length_cons,maximum_cons] <;>
    exact ⟨by omega,by omega⟩

def state (i c : ℕ) (acc input : List ℕ) : List ℕ := i::c::acc.length::acc++input

lemma symbol_state (i c : ℕ) (acc input : List ℕ) :
    symbol (state i c acc input)=(input.drop i).headI := by
  simp only [symbol,state,List.cons_append,List.drop_succ_cons,List.drop_zero,List.headI_cons]
  rw [show 3+acc.length+i=(acc.length+i)+3 by omega]
  simp only [List.drop_succ_cons]
  rw [show acc.length+i=acc.length+i from rfl,←List.drop_drop,List.drop_left]
lemma step_state (i c : ℕ) (acc input : List ℕ) :
    step (state i c acc input)=if (input.drop i).headI=1 then state (i+1) 0 (c::acc) input
      else state (i+1) (c+1) acc input := by
  unfold step
  rw [symbol_state]
  split_ifs <;> rfl

def count : List ℕ → ℕ
  | [] => 0
  | a::as => if a=0 then 0 else count as+1

def decodeAux (c : ℕ) (acc : List ℕ) : List ℕ → List ℕ
  | [] => acc
  | a::as => if a=0 then acc else if a=1 then decodeAux 0 (c::acc) as else decodeAux (c+1) acc as

def lastCounter (c : ℕ) : List ℕ → ℕ
  | [] => c
  | a::as => if a=0 then c else if a=1 then lastCounter 0 as else lastCounter (c+1) as

lemma count_le (v : List ℕ) : count v≤v.length := by
  induction v with
  | nil => rfl
  | cons a as ih => simp only [count,List.length_cons]; split_ifs <;> omega

lemma count_drop_head (v : List ℕ) : (v.drop (count v)).headI=0 := by
  induction v with
  | nil => rfl
  | cons a as ih =>
    simp only [count]
    split_ifs with h
    · simpa only [List.drop_zero,List.headI_cons] using h
    · simpa only [List.drop_succ_cons] using ih

lemma iterate_state (input pre suffix : List ℕ) (c : ℕ) (acc : List ℕ)
    (he : input=pre++suffix) :
    step^[count suffix] (state pre.length c acc input)=
      state (pre.length+count suffix) (lastCounter c suffix) (decodeAux c acc suffix) input := by
  induction suffix generalizing pre c acc with
  | nil => simp only [count,Function.iterate_zero_apply,lastCounter,decodeAux,Nat.add_zero]
  | cons a as ih =>
    by_cases h0 : a=0
    · simp only [count,h0,ite_true,Function.iterate_zero_apply,lastCounter,decodeAux,Nat.add_zero]
    · have hs : (input.drop pre.length).headI=a := by rw [he,List.drop_left]; rfl
      rw [count,ite_eq_right h0,Function.iterate_succ_apply,step_state,hs]
      have he' : input=(pre++[a])++as := by simpa only [List.append_assoc,List.singleton_append] using he
      have hp : (pre++[a]).length=pre.length+1 := by simp
      by_cases h1 : a=1
      · rw [ite_eq_left h1,←hp,ih _ _ _ he']
        simp only [lastCounter,decodeAux,h1,ite_true,List.length_append,List.length_singleton]
        congr 1
        omega
      · rw [ite_eq_right h1,←hp,ih _ _ _ he']
        simp only [lastCounter,decodeAux,h0,h1,ite_false,List.length_append,List.length_singleton]
        congr 1
        omega

lemma count_drop_ne (v : List ℕ) (i : ℕ) (hi : i<count v) : (v.drop i).headI≠0 := by
  induction v generalizing i with
  | nil => simp only [count] at hi; omega
  | cons a as ih =>
    simp only [count] at hi
    by_cases h : a=0
    · simp only [h,ite_true] at hi; omega
    · simp only [h,ite_false] at hi
      cases i with
      | zero => simpa only [List.drop_zero,List.headI_cons] using h
      | succ i => exact ih i (by omega)

lemma iterate_shape (input : List ℕ) (i : ℕ) :
    ∃ c acc,step^[i] (state 0 0 [] input)=state i c acc input := by
  induction i with
  | zero => exact ⟨0,[],rfl⟩
  | succ i ih =>
    obtain ⟨c,acc,he⟩:=ih
    rw [Function.iterate_succ_apply',he,step_state]
    split_ifs
    · exact ⟨0,c::acc,rfl⟩
    · exact ⟨c+1,acc,rfl⟩

lemma symbol_iterate (input : List ℕ) (i : ℕ) :
    symbol (step^[i] (state 0 0 [] input))=(input.drop i).headI := by
  obtain ⟨c,acc,he⟩:=iterate_shape input i
  rw [he,symbol_state]

def parsed (v : List ℕ) : List ℕ := (decodeAux 0 [] v).length::decodeAux 0 [] v++v

noncomputable def parseSize : Polynomial ℕ := C 20*(X+1)^2
lemma iterate_size (v : List ℕ) (i : ℕ) (hi : i≤count v) :
    magnitude (step^[i] (state 0 0 [] v))≤parseSize.eval (magnitude v) := by
  have hh:=iterate_length_maximum 4 1 step_safe (state 0 0 [] v) i
  have hl:=count_le v
  have hv:=length_le_magnitude v
  have hm:=maximum_le_magnitude v
  have hs:=magnitude_le_length_maximum (step^[i] (state 0 0 [] v))
  simp only [state,List.cons_append,List.nil_append,List.length_nil,List.length_cons,
    maximum_cons,Nat.zero_max,Nat.one_mul] at hh
  change (step^[i] (state 0 0 [] v)).length≤v.length+3+4*i ∧
    maximum (step^[i] (state 0 0 [] v))≤ maximum v+i at hh
  simp only [parseSize,eval_mul,eval_C,eval_pow,eval_add,eval_X,eval_one]
  have hlen : (step^[i] (state 0 0 [] v)).length≤5*(magnitude v+1) := by omega
  have hmax : maximum (step^[i] (state 0 0 [] v))+1≤2*(magnitude v+1) := by omega
  have hh:=Nat.mul_le_mul hlen hmax
  nlinarith

lemma finish_iterate (v : List ℕ) : finish (step^[count v] (state 0 0 [] v))=parsed v := by
  have h:=iterate_state v [] v 0 [] (by rfl)
  simpa only [List.length_nil,Nat.zero_add,finish,state,List.cons_append,List.nil_append,
    List.drop_succ_cons,List.drop_zero,List.headI_cons,parsed] using congrArg finish h

noncomputable def parserBound : Polynomial ℕ :=
  (X+1)*(bodyProgram.bound.comp parseSize+C 32*(parseSize+3))+C 1000*(X+1)

lemma run_parser (v : List ℕ) :
    Runs (.fix bodyProgram.code) (state 0 0 [] v) (parsed v) (parserBound.eval (magnitude v)) := by
  have hn := (count_le v).trans (length_le_magnitude v)
  have hh:=run_fix_bounded (body:=bodyProgram.code) (out:=parsed v) (state:=fun i=>step^[i] (state 0 0 [] v))
    (count v) (parseSize.eval (magnitude v)) (bodyProgram.bound.eval (parseSize.eval (magnitude v)))
    (iterate_size v) ?_ ?_
  · apply hh.mono
    simp only [parserBound,eval_add,eval_mul,eval_comp,eval_C,eval_X,eval_one,eval_ofNat]
    have h:=Nat.mul_le_mul_right
      (bodyProgram.bound.eval (parseSize.eval (magnitude v))+32*(parseSize.eval (magnitude v)+3))
      (show count v+1≤ magnitude v+1 by omega)
    omega
  · intro i hi
    have hh:=bodyProgram.run (step^[i] (state 0 0 [] v))
    have he : body (step^[i] (state 0 0 [] v))=1::step^[i+1] (state 0 0 [] v) := by
      simp only [body,symbol_iterate,ite_eq_right (count_drop_ne v i hi),Function.iterate_succ_apply']
    rw [he] at hh
    exact hh.mono (evalNat_mono _ (iterate_size v i (by omega)))
  · have hh:=bodyProgram.run (step^[count v] (state 0 0 [] v))
    have he : body (step^[count v] (state 0 0 [] v))=0::parsed v := by
      rw [body,symbol_iterate,count_drop_head,ite_eq_left rfl,finish_iterate]
    rw [he] at hh
    exact hh.mono (evalNat_mono _ (iterate_size v (count v) le_rfl))

noncomputable def initializer : PolyProgram (state 0 0 []) :=
  (PolyProgram.const 0).cons ((PolyProgram.const 0).cons ((PolyProgram.const 0).cons PolyProgram.id))

noncomputable def parserProgram : PolyProgram parsed where
  code := .comp (.fix bodyProgram.code) initializer.code
  bound := parserBound+bodyProgram.bound.comp parseSize+initializer.bound+C 2000*(X+1)
  run v := by
    apply (run_comp (initializer.run v) (run_parser v)).mono
    simp only [eval_add,eval_comp,eval_mul,eval_C,eval_X,eval_one]
    omega
  size v := by
    have hh:=bodyProgram.size (step^[count v] (state 0 0 [] v))
    rw [body,symbol_iterate,count_drop_head,ite_eq_left rfl,finish_iterate] at hh
    have hs:=evalNat_mono bodyProgram.bound (iterate_size v (count v) le_rfl)
    simp only [magnitude_cons] at hh
    simp only [eval_add,eval_comp,eval_mul,eval_C,eval_X,eval_one]
    omega
end MinUncut.Costed.UnaryWords

end OAI
