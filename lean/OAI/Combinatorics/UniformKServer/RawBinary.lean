import Mathlib
import OAI.Combinatorics.UniformKServer.RawMetric

namespace OAI

noncomputable section
                                
section

namespace UniformKServer.RawBinary
open Primrec RawCertificate
attribute [fun_prop] Primrec.list_tail

def value (w : List Bool) : ℕ := w.foldr (fun b v=>(if b then 1 else 0)+2*v) 0

@[simp] theorem value_nil : value []=0 := rfl
@[simp] theorem value_cons (b : Bool) (w : List Bool) : value (b::w)=Nat.bit b (value w) := by
  cases b <;> simp [value,Nat.bit_val,Nat.add_comm]

theorem value_bits (a : ℕ) : value a.bits=a := by
  induction a using Nat.binaryRec' with
  | zero=>rfl
  | bit b n h ih=>rw [Nat.bits_append_bit n b h,value_cons,ih]

@[fun_prop] theorem primitive_value {α : Type*} [Primcodable α] (w : α→List Bool) (hw : Primrec w) :
    Primrec (fun x=>value (w x)) := by
  unfold value
  have h : Primrec (fun p : α×(Bool×ℕ)=>(if p.2.1 then 1 else 0)+2*p.2.2) :=
    by
      simp only [←Bool.cond_eq_ite]
      exact Primrec.nat_add.comp
        (Primrec.cond (Primrec.fst.comp Primrec.snd) (Primrec.const 1) (Primrec.const 0))
        (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_foldr hw (Primrec.const 0) h.to₂

def readNat (w : List Bool) : ℕ×List Bool :=
  let a:=(w.takeWhile id).length
  let v:=w.drop (a+1)
  (value (v.take a),v.drop a)

@[simp] theorem read_natCode (a : ℕ) (w : List Bool) : readNat (natCode a++w)=(a,w) := by
  have ht : ((natCode a++w).takeWhile id).length=a.bits.length := by
    simp [natCode,List.append_assoc]
  dsimp only [readNat]
  rw [ht]
  have hd : (natCode a++w).drop (a.bits.length+1)=a.bits++w := by
    simp [natCode,List.append_assoc,List.drop_append]
  rw [hd]
  simp [value_bits]

def readQ (w : List Bool) : RawArithmetic.Q×List Bool :=
  let a:=readNat w.tail
  let b:=readNat a.2
  ((a.1,b.1-1),b.2)

@[simp] theorem read_rationalCode (a : ℚ) (w : List Bool) :
    readQ (rationalCode a++w)=(RawMetric.present a,w) := by
  simp only [readQ,rationalCode,List.cons_append,List.tail_cons,List.append_assoc,read_natCode,
    RawMetric.present]

def readMany (n : ℕ) (w : List Bool) : List RawArithmetic.Q×List Bool :=
  (List.range n).foldl (fun p _=>let a:=readQ p.2;(p.1++[a.1],a.2)) ([],w)

def input (w : List Bool) : Input :=
  let n:=readNat w
  let k:=readNat n.2
  (n.1,k.1,(readMany (n.1*n.1) k.2).1)

section Primitive
variable {α : Type*} [Primcodable α]
@[fun_prop] theorem primitive_readNat (w : α→List Bool) (hw : Primrec w) :
    Primrec (fun x=>readNat (w x)) := by
  have ht : Primrec (fun x=>(w x).takeWhile id) := (Primrec.list_takeWhile Primrec.id).comp hw
  have ha : Primrec (fun x=>(w x).takeWhile id |>.length) := Primrec.list_length.comp ht
  have hd : Primrec (fun x=>(w x).drop (((w x).takeWhile id).length+1)) :=
    Primrec.list_drop.comp (Primrec.succ.comp ha) hw
  exact Primrec.pair (primitive_value _ (Primrec.list_take.comp ha hd))
    (Primrec.list_drop.comp ha hd)
@[fun_prop] theorem primitive_readQ (w : α→List Bool) (hw : Primrec w) :
    Primrec (fun x=>readQ (w x)) := by unfold readQ;fun_prop
@[fun_prop] theorem primitive_readMany (n : α→ℕ) (w : α→List Bool) (hn : Primrec n) (hw : Primrec w) :
    Primrec (fun x=>readMany (n x) (w x)) := by
  unfold readMany
  have h : Primrec (fun p : α×((List RawArithmetic.Q×List Bool)×ℕ)=>
      let a:=readQ p.2.1.2;(p.2.1.1++[a.1],a.2)) := by fun_prop
  exact Primrec.list_foldl (Primrec.list_range.comp hn) (Primrec.pair (Primrec.const []) hw) h.to₂
@[fun_prop] theorem primitive_input (w : α→List Bool) (hw : Primrec w) :
    Primrec (fun x=>input (w x)) := by unfold input;fun_prop
end Primitive

theorem fold_read (xs : List ℚ) (w : List Bool) (ys : List RawArithmetic.Q) (m : ℕ) :
    (List.range' m xs.length).foldl (fun p _=>let a:=readQ p.2;(p.1++[a.1],a.2))
      (ys,(xs.map rationalCode).flatten++w)=(ys++xs.map RawMetric.present,w) := by
  induction xs generalizing ys m with
  | nil=>simp
  | cons x xs ih=>
    simp only [List.length_cons,List.range'_succ,List.map_cons,List.flatten_cons,
      List.append_assoc,List.foldl_cons,read_rationalCode]
    rw [ih]
    simp

theorem readMany_codes (xs : List ℚ) (w : List Bool) :
    readMany xs.length ((xs.map rationalCode).flatten++w)=(xs.map RawMetric.present,w) := by
  simpa only [readMany,List.range_eq_range',List.nil_append] using fold_read xs w [] 0

def distances {n : ℕ} (d : RationalMetric n) : List ℚ :=
  (List.ofFn fun x : Fin n=>(List.ofFn fun y : Fin n=>d.distance x y)).flatten

@[simp] theorem distances_length {n : ℕ} (d : RationalMetric n) : (distances d).length=n*n := by
  simp [distances,List.length_flatten,List.sum_ofFn,Finset.sum_const,smul_eq_mul]

theorem distance_codes {n : ℕ} (d : RationalMetric n) :
    ((distances d).map rationalCode).flatten=
      (List.ofFn fun x : Fin n =>
        (List.ofFn fun y : Fin n => rationalCode (d.distance x y)).flatten).flatten := by
  simp only [distances,List.map_flatten,List.map_ofFn,Function.comp_def]
  rw [List.flatten_flatten]
  simp only [List.map_ofFn,Function.comp_def]

@[simp] theorem input_code {n k : ℕ} (d : RationalMetric n) (s : Configuration n k) :
    input (instanceCode d s)=(n,k,(distances d).map RawMetric.present) := by
  unfold input instanceCode
  simp only [List.append_assoc,read_natCode]
  rw [←distance_codes,←distances_length d,readMany_codes]

theorem distances_ofFn {n : ℕ} (d : RationalMetric n) :
    distances d=List.ofFn (fun z : Fin (n*n)=>
      d.distance (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2) := by
  rw [List.ofFn_mul]
  unfold distances
  congr 1
  apply List.ofFn_inj.mpr
  funext x
  apply List.ofFn_inj.mpr
  funext y
  have h : (⟨x.val*n+y.val,by nlinarith [x.isLt,y.isLt]⟩ : Fin (n*n))=finProdFinEquiv (x,y) := by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.add_comm,Nat.mul_comm]
  simp only [h,Equiv.symm_apply_apply]

theorem metric_input {n : ℕ} (d : RationalMetric n) (x y : Fin n) :
    RawArithmetic.value (RawTable.dist n ((distances d).map RawMetric.present) x.val y.val)=
      d.distance x y := by
  rw [distances_ofFn]
  simp only [List.map_ofFn,Function.comp_def,RawTable.dist]
  have hh : x.val*n+y.val<n*n := by nlinarith [x.isLt,y.isLt]
  rw [List.getD_eq_getElem _ _ (by simpa using hh)]
  simp only [List.getElem_ofFn]
  have h : (⟨x.val*n+y.val,hh⟩ : Fin (n*n))=finProdFinEquiv (x,y) := by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.add_comm,Nat.mul_comm]
  rw [h,Equiv.symm_apply_apply,RawMetric.present_eq _ (d.nonneg x y)]

end UniformKServer.RawBinary

end


end

end OAI
