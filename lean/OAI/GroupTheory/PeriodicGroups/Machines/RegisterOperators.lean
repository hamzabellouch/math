import Mathlib
import OAI.GroupTheory.PeriodicGroups.Machines.ArithmeticDevices

namespace OAI

universe u v w
namespace SourceBurnside.Structured.Binary
open Program
variable {K : Type} [DecidableEq K]

def pushList (k : K) : List Bool → Program K
  | [] => .skip
  | a::w => .seq (.push k a) (pushList k w)
lemma pushList_run (k : K) (w : List Bool) (r : Store K) :
    Run (pushList k w) r (w.length+1) (Function.update r k (r k++w)) := by
  induction w generalizing r with
  | nil => simpa [pushList] using Run.skip r
  | cons a w ih =>
    have H := Run.seq (.push k a) (pushList k w) r _ _ 1 (w.length+1)
      (Run.push r k a) (ih (Function.update r k (r k++[a])))
    simpa [pushList,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using H

def dropN (k : K) : ℕ → Program K
  | 0 => .skip
  | n+1 => .pop k (fun _ => dropN k n)
lemma dropN_run (k : K) (m n : ℕ) (r : Store K) (hr : r k=List.replicate n false) :
    Run (dropN k m) r (m+1) (Function.update r k (List.replicate (n-m) false)) := by
  induction m generalizing n r with
  | zero => simpa [dropN,←hr] using Run.skip r
  | succ m ih =>
    let s := Function.update r k (r k).dropLast
    have hs : s k=List.replicate (n-1) false := by simp [s,hr,List.dropLast_replicate]
    have H := Run.pop r k (fun _ => dropN k m) (m+1) _ (ih (n-1) s hs)
    simpa [dropN,s,Nat.sub_sub,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using H

end SourceBurnside.Structured.Binary

namespace SourceBurnside.Structured.Device
section
open Program Binary
variable {ι : Type} [DecidableEq ι]
namespace Constant
abbrev L (ι : Type) := ι ⊕ Fin 2

def program (i : ι) (bs : List Bool) : Program (L ι) :=
  .seq (copy (.inl i) (.inr 0) (.inr 1)) (.seq (mapInPlace (fun _ => false) (.inr 0) (.inr 1))
    (.seq (dropN (.inr 0) bs.length) (pushList (.inr 0) bs)))

lemma program_run (i : ι) (bs : List Bool) (xs : ι → List Bool) (n : ℕ) (hs : (xs i).length=n) :
    Run (program i bs) (input xs) (9*n+2*bs.length+6)
      (result xs (0:Fin 2) (List.replicate (n-bs.length) false++bs)) := by
  let r : Store (L ι) := input xs
  let s := Function.update r (.inr (0:Fin 2)) (xs i)
  have H1 := copy_run (.inl i) (.inr (0:Fin 2)) (.inr 1) (by simp) (by simp) (by simp) r (by rfl)
  change Run (copy (.inl i) (.inr (0:Fin 2)) (.inr 1)) r (5*(xs i).length+2) s at H1
  rw [hs] at H1
  have H2 := mapInPlace_run (fun _ => false) (.inr (0:Fin 2)) (.inr 1) (by simp) s
    (by simp [s,r,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  let z := Function.update r (.inr (0:Fin 2)) (List.replicate n false)
  have hsz : Function.update s (.inr 0) ((s (.inr 0)).map (fun _ => false))=z := by
    simp [s,z,hs]
  rw [hsz] at H2
  have hl : (s (.inr 0)).length=n := by simp [s,hs]
  rw [hl] at H2
  have H3 := dropN_run (.inr (0:Fin 2)) bs.length n z (by simp [z])
  let t := Function.update r (.inr (0:Fin 2)) (List.replicate (n-bs.length) false)
  change Run (dropN (.inr (0:Fin 2)) bs.length) z (bs.length+1)
    (Function.update z (.inr 0) (List.replicate (n-bs.length) false)) at H3
  have hzt : Function.update z (.inr 0) (List.replicate (n-bs.length) false)=t := by simp [z,t]
  rw [hzt] at H3
  have H4 := pushList_run (.inr (0:Fin 2)) bs t
  have htf : Function.update t (.inr 0) (t (.inr 0)++bs)=
      result xs (0:Fin 2) (List.replicate (n-bs.length) false++bs) := by
    simp [t,result,r]
  rw [htf] at H4
  have H := Run.seq _ _ _ _ _ _ _ H1 (Run.seq _ _ _ _ _ _ _ H2 (Run.seq _ _ _ _ _ _ _ H3 H4))
  convert H using 1 <;> first | rfl | omega

lemma value_false (n : ℕ) : Add.value (List.replicate n false)=0 := by
  exact Divide.zero_value n
lemma value_bits (n : ℕ) : Add.value n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => simp [Add.value]
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    cases b <;> simp [Add.value,ih,Nat.bit,Add.bit]
    omega

end Constant

def constant (i : ι) (a : ℕ) : Realizer (fun _ : ι → ℕ => a) (fun n _ => a.bits.length≤n) where
  W := Fin 2
  finiteW := inferInstance
  eqW := inferInstance
  out := 0
  program := Constant.program i a.bits.reverse
  coefficient := 2*a.bits.length+15
  spec := by
    intro n hn xs hs hp
    let bs := a.bits.reverse
    let y := List.replicate (n-bs.length) false++bs
    have hl : bs.length≤n := by simpa [bs] using hp
    refine ⟨9*n+2*bs.length+6,y,?_,?_,?_,Constant.program_run i bs xs n (hs i)⟩
    · dsimp [bs];nlinarith [sq_nonneg (n:ℤ)]
    · simp [y];omega
    · simp [y,List.reverse_append,Add.value_append,Constant.value_false,bs,Constant.value_bits]

end

section
open Program Binary

namespace AddOperator
abbrev L := Fin 2 ⊕ Fin 4

def load : Program L := .seq (copy (Sum.inl 0) (Sum.inr 0) (Sum.inr 2))
  (.seq (copy (Sum.inl 1) (Sum.inr 1) (Sum.inr 2)) (.push (Sum.inr 3) false))
def program : Program L := .seq load (.seq (Add.fixedAdd.relabel Sum.inr) (clear (Sum.inr 3)))

def loaded (xs : Fin 2 → List Bool) : Store L := Sum.elim xs
  (Add.store (xs 0).reverse (xs 1).reverse [] false)

def first (xs : Fin 2 → List Bool) : Store L := Function.update (input xs) (Sum.inr 0) (xs 0)
def second (xs : Fin 2 → List Bool) : Store L := Function.update (first xs) (Sum.inr 1) (xs 1)

lemma load_run (xs : Fin 2 → List Bool) (n : ℕ) (hs : ∀i,(xs i).length=n) :
    Run load (input xs) (10*n+5) (loaded xs) := by
  have h1 := copy_run (Sum.inl (0:Fin 2)) (Sum.inr (0:Fin 4)) (Sum.inr 2) (by simp) (by simp) (by simp)
    (input xs) (by rfl)
  change Run (copy (Sum.inl (0:Fin 2)) (Sum.inr (0:Fin 4)) (Sum.inr 2)) (input xs)
    (5*(xs 0).length+2) (first xs) at h1
  rw [hs] at h1
  have h2 := copy_run (Sum.inl (1:Fin 2)) (Sum.inr (1:Fin 4)) (Sum.inr 2) (by simp) (by simp) (by simp)
    (first xs) (by simp [first,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have he2 : Function.update (first xs) (Sum.inr 1) ((first xs) (Sum.inr 1)++(first xs) (Sum.inl 1))=second xs := by
    simp [second,first,input,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he2] at h2
  have hl2 : ((first xs) (Sum.inl 1)).length=n := by simp [first,input,hs,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [hl2] at h2
  have h3 := Run.push (second xs) (Sum.inr (3:Fin 4)) false
  have he3 : Function.update (second xs) (Sum.inr 3) ((second xs) (Sum.inr 3)++[false])=loaded xs := by
    funext k;cases k with
    | inl i => simp [loaded,second,first,input,-Sum.update_elim_inr,-Sum.elim_update_right]
    | inr i => fin_cases i <;> simp [loaded,second,first,input,Add.store,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he3] at h3
  have H := Run.seq (copy (Sum.inl 0) (Sum.inr 0) (Sum.inr 2)) _ _ _ _ _ _ h1
    (Run.seq (copy (Sum.inl 1) (Sum.inr 1) (Sum.inr 2)) (.push (Sum.inr 3) false) _ _ _ _ _ h2 h3)
  convert H using 1 <;> first | rfl | omega

lemma program_run (xs : Fin 2 → List Bool) (n : ℕ) (hs : ∀i,(xs i).length=n) :
    let z := (Add.scan (xs 0).reverse (xs 1).reverse false).1
    Run program (input xs) (17*n+10) (result xs (0:Fin 4) z.reverse) := by
  dsimp only
  let a := (xs 0).reverse
  let b := (xs 1).reverse
  let z := (Add.scan a b false).1
  let c := (Add.scan a b false).2.2
  have he : a.length=b.length := by simp only [a,b,List.length_reverse,hs]
  have h1 := load_run xs n hs
  let R : Store L := Sum.elim xs (Add.store z [] [] c)
  have h2 : Run (Add.fixedAdd.relabel Sum.inr) (loaded xs) (7*a.length+2) R := by
    refine (Add.fixedAdd_run a b false he).relabel_to Sum.inr Sum.inr_injective (loaded xs) R
      (by intro k;rfl) (by intro k;rfl) ?_
    intro l hl;cases l with
    | inl i => rfl
    | inr k => exact False.elim (hl k rfl)
  have hl : a.length=n := by simp [a,hs]
  rw [hl] at h2
  have h3 := clear_run (Sum.inr (3:Fin 4)) R
  have he3 : Function.update R (Sum.inr 3) []=result xs (0:Fin 4) z.reverse := by
    funext k;cases k with
    | inl i => simp [R,result,input,-Sum.update_elim_inr,-Sum.elim_update_right]
    | inr i => fin_cases i <;> simp [R,result,input,Add.store,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he3] at h3
  change Run (clear (Sum.inr (3:Fin 4))) R 3 (result xs 0 z.reverse) at h3
  have H := Run.seq load _ _ _ _ _ _ h1
    (Run.seq (Add.fixedAdd.relabel Sum.inr) (clear (Sum.inr 3)) _ _ _ _ _ h2 h3)
  convert H using 1 <;> first | rfl | omega

end AddOperator

def add : Realizer (fun vs : Fin 2 → ℕ => vs 0+vs 1) (fun n vs => vs 0+vs 1<2^n) where
  W := Fin 4
  finiteW := inferInstance
  eqW := inferInstance
  out := 0
  program := AddOperator.program
  coefficient := 27
  spec := by
    intro n hn xs hs hpre
    let a := (xs 0).reverse
    let b := (xs 1).reverse
    let z := (Add.scan a b false).1
    have he : a.length=b.length := by simp only [a,b,List.length_reverse,hs]
    have hl : a.length=n := by simp [a,hs]
    have hz : z.length=n := (Add.scan_length a b false).trans hl
    refine ⟨17*n+10,z.reverse,by nlinarith,by simpa using hz,?_,AddOperator.program_run xs n hs⟩
    simp only [List.reverse_reverse]
    change Add.value z=Add.value a+Add.value b
    change Add.value a+Add.value b<2^n at hpre
    have hb : Add.value a+Add.value b+Add.bit false<2^a.length := by
      simpa only [Add.bit,Bool.false_eq_true,↓reduceIte,Nat.add_zero,hl] using hpre
    simpa only [Add.bit,Bool.false_eq_true,↓reduceIte,Nat.add_zero] using (Add.scan_exact a b false he hb).1

end

section
open Program Binary

namespace SubOperator
abbrev L := Fin 2 ⊕ Fin 4

def load : Program L := .seq (copy (Sum.inl 0) (Sum.inr 0) (Sum.inr 2))
  (.seq (copy (Sum.inl 1) (Sum.inr 1) (Sum.inr 2)) (.push (Sum.inr 3) true))
def program : Program L := .seq load (.seq (Add.fixedSubtract.relabel Sum.inr) (clear (Sum.inr 3)))

def loaded (xs : Fin 2 → List Bool) : Store L := Sum.elim xs
  (Add.store (xs 0).reverse (xs 1).reverse [] true)

def first (xs : Fin 2 → List Bool) : Store L := Function.update (input xs) (Sum.inr 0) (xs 0)
def second (xs : Fin 2 → List Bool) : Store L := Function.update (first xs) (Sum.inr 1) (xs 1)

lemma load_run (xs : Fin 2 → List Bool) (n : ℕ) (hs : ∀i,(xs i).length=n) :
    Run load (input xs) (10*n+5) (loaded xs) := by
  have h1 := copy_run (Sum.inl (0:Fin 2)) (Sum.inr (0:Fin 4)) (Sum.inr 2) (by simp) (by simp) (by simp)
    (input xs) (by rfl)
  change Run (copy (Sum.inl (0:Fin 2)) (Sum.inr (0:Fin 4)) (Sum.inr 2)) (input xs)
    (5*(xs 0).length+2) (first xs) at h1
  rw [hs] at h1
  have h2 := copy_run (Sum.inl (1:Fin 2)) (Sum.inr (1:Fin 4)) (Sum.inr 2) (by simp) (by simp) (by simp)
    (first xs) (by simp [first,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have he2 : Function.update (first xs) (Sum.inr 1) ((first xs) (Sum.inr 1)++(first xs) (Sum.inl 1))=second xs := by
    simp [second,first,input,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he2] at h2
  have hl2 : ((first xs) (Sum.inl 1)).length=n := by simp [first,input,hs,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [hl2] at h2
  have h3 := Run.push (second xs) (Sum.inr (3:Fin 4)) true
  have he3 : Function.update (second xs) (Sum.inr 3) ((second xs) (Sum.inr 3)++[true])=loaded xs := by
    funext k;cases k with
    | inl i => simp [loaded,second,first,input,-Sum.update_elim_inr,-Sum.elim_update_right]
    | inr i => fin_cases i <;> simp [loaded,second,first,input,Add.store,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he3] at h3
  have H := Run.seq (copy (Sum.inl 0) (Sum.inr 0) (Sum.inr 2)) _ _ _ _ _ _ h1
    (Run.seq (copy (Sum.inl 1) (Sum.inr 1) (Sum.inr 2)) (.push (Sum.inr 3) true) _ _ _ _ _ h2 h3)
  convert H using 1 <;> first | rfl | omega

lemma program_run (xs : Fin 2 → List Bool) (n : ℕ) (hs : ∀i,(xs i).length=n) :
    let z := (Add.scan (xs 0).reverse ((xs 1).reverse.map not) true).1
    Run program (input xs) (21*n+12) (result xs (0:Fin 4) z.reverse) := by
  dsimp only
  let a := (xs 0).reverse
  let b := (xs 1).reverse
  let z := (Add.scan a (b.map not) true).1
  let c := (Add.scan a (b.map not) true).2.2
  have he : a.length=b.length := by simp only [a,b,List.length_reverse,hs]
  have h1 := load_run xs n hs
  let R : Store L := Sum.elim xs (Add.store z [] [] c)
  have h2 : Run (Add.fixedSubtract.relabel Sum.inr) (loaded xs) (11*a.length+4) R := by
    refine (Add.fixedSubtract_run a b he).relabel_to Sum.inr Sum.inr_injective (loaded xs) R
      (by intro k;rfl) (by intro k;rfl) ?_
    intro l hl;cases l with
    | inl i => rfl
    | inr k => exact False.elim (hl k rfl)
  have hl : a.length=n := by simp [a,hs]
  rw [hl] at h2
  have h3 := clear_run (Sum.inr (3:Fin 4)) R
  have he3 : Function.update R (Sum.inr 3) []=result xs (0:Fin 4) z.reverse := by
    funext k;cases k with
    | inl i => simp [R,result,input,-Sum.update_elim_inr,-Sum.elim_update_right]
    | inr i => fin_cases i <;> simp [R,result,input,Add.store,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he3] at h3
  change Run (clear (Sum.inr (3:Fin 4))) R 3 (result xs 0 z.reverse) at h3
  have H := Run.seq load _ _ _ _ _ _ h1
    (Run.seq (Add.fixedSubtract.relabel Sum.inr) (clear (Sum.inr 3)) _ _ _ _ _ h2 h3)
  convert H using 1 <;> first | rfl | omega

end SubOperator

def subtract : Realizer (fun vs : Fin 2 → ℕ => vs 0-vs 1) (fun _ vs => vs 1≤vs 0) where
  W := Fin 4
  finiteW := inferInstance
  eqW := inferInstance
  out := 0
  program := SubOperator.program
  coefficient := 33
  spec := by
    intro n hn xs hs hpre
    let a := (xs 0).reverse
    let b := (xs 1).reverse
    let z := (Add.scan a (b.map not) true).1
    have he : a.length=b.length := by simp only [a,b,List.length_reverse,hs]
    have hl : a.length=n := by simp [a,hs]
    have hz : z.length=n := (Add.scan_length a (b.map not) true).trans hl
    refine ⟨21*n+12,z.reverse,by nlinarith,by simpa using hz,?_,SubOperator.program_run xs n hs⟩
    simp only [List.reverse_reverse]
    exact Add.subtract_exact a b he hpre

end

section
open Program Binary
namespace CompareOperator
abbrev L := Fin 2 ⊕ Fin 4

def finish : Program L := .seq (mapInPlace (fun _ => false) (.inr 0) (.inr 2))
  (.pop (.inr 0) (fun _ => .pop (.inr 3) (fun b => .push (.inr 0) (b.getD false))))
def program : Program L := .seq SubOperator.load (.seq (Add.fixedSubtract.relabel Sum.inr) finish)

def padded (n : ℕ) (b : Bool) : List Bool := List.replicate (n-1) false++[b]
lemma padded_length (n : ℕ) (hn : 0<n) (b : Bool) : (padded n b).length=n := by simp [-Sum.update_elim_inr,-Sum.elim_update_right,padded];omega
lemma padded_value (n : ℕ) (b : Bool) : Add.value (padded n b).reverse=Add.bit b := by
  simp [-Sum.update_elim_inr,-Sum.elim_update_right,padded,List.reverse_append,Add.value,Constant.value_false]

lemma finish_run (xs : Fin 2 → List Bool) (z : List Bool) (c : Bool) :
    Run finish (Sum.elim xs (Add.store z [] [] c)) (4*z.length+5)
      (result xs (0:Fin 4) (padded z.length c)) := by
  let R : Store L := Sum.elim xs (Add.store z [] [] c)
  let S := Function.update R (.inr (0:Fin 4)) (List.replicate z.length false)
  have h1 := mapInPlace_run (fun _ => false) (.inr (0:Fin 4)) (.inr 2) (by simp) R (by rfl)
  have he : Function.update R (.inr 0) ((R (.inr 0)).map (fun _ => false))=S := by simp [-Sum.update_elim_inr,-Sum.elim_update_right,S,R,Add.store]
  rw [he] at h1
  have hl : (R (.inr 0)).length=z.length := by simp [-Sum.update_elim_inr,-Sum.elim_update_right,R,Add.store]
  rw [hl] at h1
  let U := Function.update S (.inr (0:Fin 4)) (List.replicate (z.length-1) false)
  let V := Function.update U (.inr (3:Fin 4)) []
  have hpush := Run.push V (.inr (0:Fin 4)) c
  have hpf : Function.update V (.inr 0) (V (.inr 0)++[c])=result xs (0:Fin 4) (padded z.length c) := by
    funext k;cases k with
    | inl i => simp [-Sum.update_elim_inr,-Sum.elim_update_right,V,U,S,R,result,input]
    | inr i => fin_cases i <;> simp [-Sum.update_elim_inr,-Sum.elim_update_right,V,U,S,R,result,input,Add.store,padded]
  rw [hpf] at hpush
  have hc : U (.inr 3)=[c] := by simp [-Sum.update_elim_inr,-Sum.elim_update_right,U,S,R,Add.store]
  have h2 : Run (.pop (.inr (3:Fin 4)) (fun b => Program.push (.inr 0) (b.getD false))) U 2
      (result xs 0 (padded z.length c)) := by
    refine Run.pop U (.inr 3) _ 1 _ ?_
    simpa [hc,V] using hpush
  have hz : S (.inr 0)=List.replicate z.length false := by simp [-Sum.update_elim_inr,-Sum.elim_update_right,S]
  have h3 : Run (.pop (.inr (0:Fin 4)) (fun _ => Program.pop (.inr 3) (fun b => .push (.inr 0) (b.getD false)))) S 3
      (result xs 0 (padded z.length c)) := by
    refine Run.pop S (.inr 0) _ 2 _ ?_
    simpa [hz,U,List.dropLast_replicate] using h2
  have H := Run.seq _ _ _ _ _ _ _ h1 h3
  convert H using 1
  rfl

lemma program_run (xs : Fin 2 → List Bool) (n : ℕ) (hs : ∀i,(xs i).length=n) :
    let c := (Add.scan (xs 0).reverse ((xs 1).reverse.map not) true).2.2
    Run program (input xs) (25*n+14) (result xs (0:Fin 4) (padded n c)) := by
  dsimp only
  let a := (xs 0).reverse
  let b := (xs 1).reverse
  let z := (Add.scan a (b.map not) true).1
  let c := (Add.scan a (b.map not) true).2.2
  have he : a.length=b.length := by simp [-Sum.update_elim_inr,-Sum.elim_update_right,a,b,hs]
  have h1 := SubOperator.load_run xs n hs
  let R : Store L := Sum.elim xs (Add.store z [] [] c)
  have h2 : Run (Add.fixedSubtract.relabel Sum.inr) (SubOperator.loaded xs) (11*a.length+4) R := by
    refine (Add.fixedSubtract_run a b he).relabel_to Sum.inr Sum.inr_injective (SubOperator.loaded xs) R
      (by intro k;rfl) (by intro k;rfl) ?_
    intro l hl;cases l with
    | inl i => rfl
    | inr k => exact False.elim (hl k rfl)
  have hl : a.length=n := by simp [-Sum.update_elim_inr,-Sum.elim_update_right,a,hs]
  have hz : z.length=n := (Add.scan_length a (b.map not) true).trans hl
  rw [hl] at h2
  have h3 := finish_run xs z c
  rw [hz] at h3
  have H := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2 h3)
  convert H using 1 <;> first | rfl | omega
end CompareOperator

def lessEqualReversed : Realizer (fun vs : Fin 2 → ℕ => if vs 1≤vs 0 then 1 else 0) (fun _ _ => True) where
  W := Fin 4
  finiteW := inferInstance
  eqW := inferInstance
  out := 0
  program := CompareOperator.program
  coefficient := 39
  spec := by
    intro n hn xs hs hpre
    let a := (xs 0).reverse
    let b := (xs 1).reverse
    let c := (Add.scan a (b.map not) true).2.2
    have he : a.length=b.length := by simp [-Sum.update_elim_inr,-Sum.elim_update_right,a,b,hs]
    refine ⟨25*n+14,CompareOperator.padded n c,by nlinarith,CompareOperator.padded_length n hn c,?_,CompareOperator.program_run xs n hs⟩
    rw [CompareOperator.padded_value]
    change Add.bit c=if Add.value b≤Add.value a then 1 else 0
    have hh : c=true ↔ Add.value b≤Add.value a := Add.subtract_carry a b he
    cases hc : c <;> simp_all [Add.bit]

end

section
open Program Binary
namespace MultiplyOperator
abbrev L := Fin 2 ⊕ Fin 6

def load : Program L := .seq (copy (.inl 0) (.inr 0) (.inr 4))
  (.seq (mapInPlace (fun _ => false) (.inr 0) (.inr 4))
  (.seq (copy (.inl 0) (.inr 1) (.inr 4)) (copy (.inl 1) (.inr 2) (.inr 4))))
def program : Program L := .seq load (.seq (Multiply.program.relabel Sum.inr) (clear (.inr 1)))
def loaded (xs : Fin 2 → List Bool) (n : ℕ) : Store L :=
  Sum.elim xs (Multiply.store (List.replicate n false) (xs 0).reverse (xs 1).reverse)

lemma load_run (xs : Fin 2 → List Bool) (n : ℕ) (hs : ∀i,(xs i).length=n) :
    Run load (input xs) (19*n+8) (loaded xs n) := by
  let R : Store L := input xs
  let R1 := Function.update R (.inr (0:Fin 6)) (xs 0)
  let R2 := Function.update R (.inr (0:Fin 6)) (List.replicate n false)
  let R3 := Function.update R2 (.inr (1:Fin 6)) (xs 0)
  have h1 := copy_run (.inl (0:Fin 2)) (.inr (0:Fin 6)) (.inr 4) (by simp) (by simp) (by simp) R (by rfl)
  change Run (copy (.inl (0:Fin 2)) (.inr (0:Fin 6)) (.inr 4)) R (5*(xs 0).length+2) R1 at h1
  rw [hs] at h1
  have h2 := mapInPlace_run (fun _ => false) (.inr (0:Fin 6)) (.inr 4) (by simp) R1
    (by simp [R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have he2 : Function.update R1 (.inr 0) ((R1 (.inr 0)).map (fun _ => false))=R2 := by simp [R1,R2,hs]
  rw [he2] at h2
  have hl2 : (R1 (.inr 0)).length=n := by simp [R1,hs]
  rw [hl2] at h2
  have h3 := copy_run (.inl (0:Fin 2)) (.inr (1:Fin 6)) (.inr 4) (by simp) (by simp) (by simp) R2
    (by simp [R2,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have he3 : Function.update R2 (.inr 1) (R2 (.inr 1)++R2 (.inl 0))=R3 := by
    simp [R3,R2,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he3] at h3
  have hl3 : (R2 (.inl 0)).length=n := by simp [R2,R,input,hs,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [hl3] at h3
  have h4 := copy_run (.inl (1:Fin 2)) (.inr (2:Fin 6)) (.inr 4) (by simp) (by simp) (by simp) R3
    (by simp [R3,R2,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have he4 : Function.update R3 (.inr 2) (R3 (.inr 2)++R3 (.inl 1))=loaded xs n := by
    funext k;cases k with
    | inl i => simp [loaded,R3,R2,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
    | inr i => fin_cases i <;> simp [loaded,Multiply.store,R3,R2,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he4] at h4
  have hl4 : (R3 (.inl 1)).length=n := by simp [R3,R2,R,input,hs,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [hl4] at h4
  have H := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2 (Run.seq _ _ _ _ _ _ _ h3 h4))
  convert H using 1 <;> first | rfl | omega

lemma program_run (xs : Fin 2 → List Bool) (n : ℕ) (hn : 0<n) (hs : ∀i,(xs i).length=n) :
    let z := (Multiply.scan (List.replicate n false) (xs 0).reverse (xs 1).reverse).1
    Run program (input xs) (21*n+9+Multiply.time n (xs 1).reverse) (result xs (0:Fin 6) z.reverse) := by
  dsimp only
  let acc := List.replicate n false
  let x := (xs 0).reverse
  let y := (xs 1).reverse
  let z := (Multiply.scan acc x y).1
  let xx := (Multiply.scan acc x y).2
  have hl : x.length=n := by simp [x,hs]
  have ha : acc.length=x.length := by simp [acc,hl]
  have hx : x≠[] := by intro hh;rw [hh] at hl;simp at hl;omega
  have h1 := load_run xs n hs
  let R : Store L := Sum.elim xs (Multiply.store z xx [])
  have h2 : Run (Multiply.program.relabel Sum.inr) (loaded xs n) (Multiply.time n y) R := by
    have hh := (Multiply.program_run acc x y hx ha).relabel_to Sum.inr Sum.inr_injective (loaded xs n) R
      (by intro k;rfl) (by intro k;rfl) (by
        intro l hl;cases l with
        | inl i => rfl
        | inr k => exact False.elim (hl k rfl))
    simpa [hl] using hh
  have h3 := clear_run (.inr (1:Fin 6)) R
  have he3 : Function.update R (.inr 1) []=result xs (0:Fin 6) z.reverse := by
    funext k;cases k with
    | inl i => simp [R,result,input,-Sum.update_elim_inr,-Sum.elim_update_right]
    | inr i => fin_cases i <;> simp [R,result,input,Multiply.store,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he3] at h3
  have hl3 : (R (.inr 1)).length=n := by
    have hh := (Multiply.scan_length acc x y hx ha).2
    simp only [R,Sum.elim_inr,Multiply.store,Matrix.cons_val_one,Matrix.cons_val_zero,List.length_reverse]
    exact hh.trans hl
  rw [hl3] at h3
  have H := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2 h3)
  change Run program (input xs) (21*n+9+Multiply.time n y) (result xs (0:Fin 6) z.reverse)
  convert H using 1 <;> first | rfl | omega
end MultiplyOperator

def multiply : Realizer (fun vs : Fin 2 → ℕ => vs 0*vs 1) (fun n vs => vs 0*vs 1<2^n) where
  W := Fin 6
  finiteW := inferInstance
  eqW := inferInstance
  out := 0
  program := MultiplyOperator.program
  coefficient := 42
  spec := by
    intro n hn xs hs hpre
    let acc := List.replicate n false
    let x := (xs 0).reverse
    let y := (xs 1).reverse
    let z := (Multiply.scan acc x y).1
    have hl : x.length=n := by simp [x,hs]
    have hy : y.length=n := by simp [y,hs]
    have ha : acc.length=x.length := by simp [acc,hl]
    have hx : x≠[] := by intro hh;rw [hh] at hl;simp at hl;omega
    have hz : z.length=n := (Multiply.scan_length acc x y hx ha).1.trans (by simp [acc])
    refine ⟨21*n+9+Multiply.time n y,z.reverse,?_,by simpa using hz,?_,MultiplyOperator.program_run xs n hn hs⟩
    · have ht := Multiply.time_bound n y
      rw [hy] at ht
      nlinarith
    · simp only [List.reverse_reverse]
      have hv := Multiply.scan_value acc x y hx ha
      simp only [acc,Constant.value_false,Nat.zero_add,hl] at hv
      exact hv.trans (Nat.mod_eq_of_lt hpre)

end

open Program Binary
namespace DivideOperator
abbrev L := Fin 2 ⊕ Fin 8

def load : Program L := .seq (copy (.inl 0) (.inr 0) (.inr 6))
  (.seq (mapInPlace (fun _ => false) (.inr 0) (.inr 6))
  (.seq (copy (.inr 0) (.inr 1) (.inr 6))
  (.seq (copy (.inl 1) (.inr 2) (.inr 6))
  (.seq (copy (.inl 0) (.inr 4) (.inr 6)) (move (.inr 4) (.inr 3))))))
def chosen (rem : Bool) : Fin 8 := if rem then 1 else 0
def other (rem : Bool) : Fin 8 := if rem then 0 else 1
def program (rem : Bool) : Program L := .seq load (.seq (Divide.program.relabel Sum.inr)
  (.seq (clear (.inr (other rem))) (clear (.inr 2))))
def loaded (xs : Fin 2 → List Bool) (n : ℕ) : Store L :=
  Sum.elim xs (Divide.store (List.replicate n false) (List.replicate n false) (xs 1).reverse (xs 0))

lemma load_run (xs : Fin 2 → List Bool) (n : ℕ) (hs : ∀i,(xs i).length=n) :
    Run load (input xs) (26*n+11) (loaded xs n) := by
  let R : Store L := input xs
  let R1 := Function.update R (.inr (0:Fin 8)) (xs 0)
  let R2 := Function.update R (.inr (0:Fin 8)) (List.replicate n false)
  let R3 := Function.update R2 (.inr (1:Fin 8)) (List.replicate n false)
  let R4 := Function.update R3 (.inr (2:Fin 8)) (xs 1)
  let R5 := Function.update R4 (.inr (4:Fin 8)) (xs 0)
  have h1 := copy_run (.inl (0:Fin 2)) (.inr (0:Fin 8)) (.inr 6) (by simp) (by simp) (by simp) R (by rfl)
  change Run (copy (.inl (0:Fin 2)) (.inr (0:Fin 8)) (.inr 6)) R (5*(xs 0).length+2) R1 at h1
  rw [hs] at h1
  have h2 := mapInPlace_run (fun _ => false) (.inr (0:Fin 8)) (.inr 6) (by simp) R1
    (by simp [R1,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have he2 : Function.update R1 (.inr 0) ((R1 (.inr 0)).map (fun _ => false))=R2 := by simp [R1,R2,hs]
  rw [he2] at h2
  have hl2 : (R1 (.inr 0)).length=n := by simp [R1,hs]
  rw [hl2] at h2
  have h3 := copy_run (.inr (0:Fin 8)) (.inr (1:Fin 8)) (.inr 6) (by simp) (by simp) (by simp) R2
    (by simp [R2,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have he3 : Function.update R2 (.inr 1) (R2 (.inr 1)++R2 (.inr 0))=R3 := by
    simp [R3,R2,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he3] at h3
  have hl3 : (R2 (.inr 0)).length=n := by simp [R2]
  rw [hl3] at h3
  have h4 := copy_run (.inl (1:Fin 2)) (.inr (2:Fin 8)) (.inr 6) (by simp) (by simp) (by simp) R3
    (by simp [R3,R2,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have he4 : Function.update R3 (.inr 2) (R3 (.inr 2)++R3 (.inl 1))=R4 := by
    simp [R4,R3,R2,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he4] at h4
  have hl4 : (R3 (.inl 1)).length=n := by simp [R3,R2,R,input,hs,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [hl4] at h4
  have h5 := copy_run (.inl (0:Fin 2)) (.inr (4:Fin 8)) (.inr 6) (by simp) (by simp) (by simp) R4
    (by simp [R4,R3,R2,R,input,-Sum.update_elim_inr,-Sum.elim_update_right])
  have he5 : Function.update R4 (.inr 4) (R4 (.inr 4)++R4 (.inl 0))=R5 := by
    simp [R5,R4,R3,R2,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he5] at h5
  have hl5 : (R4 (.inl 0)).length=n := by simp [R4,R3,R2,R,input,hs,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [hl5] at h5
  have h6 := move_run (.inr (4:Fin 8)) (.inr 3) (by simp) R5
  have he6 : Function.update (Function.update R5 (.inr 4) []) (.inr 3) (R5 (.inr 3)++(R5 (.inr 4)).reverse)=loaded xs n := by
    funext k;cases k with
    | inl i => simp [loaded,R5,R4,R3,R2,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
    | inr i => fin_cases i <;> simp [loaded,Divide.store,R5,R4,R3,R2,R,input,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he6] at h6
  have hl6 : (R5 (.inr 4)).length=n := by simp [R5,hs]
  rw [hl6] at h6
  have H := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2 (Run.seq _ _ _ _ _ _ _ h3
    (Run.seq _ _ _ _ _ _ _ h4 (Run.seq _ _ _ _ _ _ _ h5 h6))))
  convert H using 1 <;> first | rfl | omega

lemma finish_run (xs : Fin 2 → List Bool) (q r d : List Bool) (rem : Bool) (n : ℕ)
    (hs : q.length=n ∧ r.length=n ∧ d.length=n) :
    Run (.seq (clear (.inr (other rem))) (clear (.inr (2:Fin 8)))) (Sum.elim xs (Divide.store q r d []))
      (4*n+2) (result xs (chosen rem) (if rem then r.reverse else q.reverse)) := by
  let R : Store L := Sum.elim xs (Divide.store q r d [])
  have h1 := clear_run (.inr (other rem)) R
  have hl1 : (R (.inr (other rem))).length=n := by
    cases rem <;> simp [R,other,Divide.store,hs.1,hs.2.1]
  rw [hl1] at h1
  let S := Function.update R (.inr (other rem)) []
  have h2 := clear_run (.inr (2:Fin 8)) S
  have hl2 : (S (.inr 2)).length=n := by cases rem <;> simp [S,R,other,Divide.store,hs.2.2,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [hl2] at h2
  have he2 : Function.update S (.inr 2) []=result xs (chosen rem) (if rem then r.reverse else q.reverse) := by
    funext k;cases k with
    | inl i => cases rem <;> simp [S,R,chosen,other,result,input,-Sum.update_elim_inr,-Sum.elim_update_right]
    | inr i => cases rem <;> fin_cases i <;> simp [S,R,chosen,other,result,input,Divide.store,-Sum.update_elim_inr,-Sum.elim_update_right]
  rw [he2] at h2
  have H := Run.seq _ _ _ _ _ _ _ h1 h2
  convert H using 1
  first | rfl | omega

lemma program_correct (xs : Fin 2 → List Bool) (n : ℕ) (hn : 0<n) (hs : ∀i,(xs i).length=n)
    (hd : 0<values xs 1) (hd2 : 2*values xs 1≤2^n) (rem : Bool) :
    ∃t y,t≤101*(n+1)^2 ∧ y.length=n ∧
      Add.value y.reverse=(if rem then values xs 0%values xs 1 else values xs 0/values xs 1) ∧
      Run (program rem) (input xs) t (result xs (chosen rem) y) := by
  let d := (xs 1).reverse
  let ys := xs 0
  let z := List.replicate n false
  let qr := Divide.scan z z d ys
  have hdl : d.length=n := by simp [d,hs]
  have hzl : z.length=n := by simp [z]
  have hzn : z≠[] := by simp [z,hn.ne']
  have hi : Add.value ys.reverse<2^d.length := by rw [hdl];simpa [ys,←hs 0] using Add.value_lt (xs 0).reverse
  have hc := Divide.division d ys hd (hdl ▸ hd2) hi
  change Add.value (Divide.scan (List.replicate d.length false) (List.replicate d.length false) d ys).1=_ ∧ _ at hc
  rw [hdl] at hc
  obtain ⟨hq,hr,t,ht,htRun⟩ := hc
  have hqrl := Divide.scan_lengths z z d ys rfl hzn
  have hql : qr.1.length=n := hqrl.1.trans hzl
  have hrl : qr.2.length=n := hqrl.2.trans hzl
  let R : Store L := Sum.elim xs (Divide.store qr.1 qr.2 d [])
  have H1 := load_run xs n hs
  have H2 : Run (Divide.program.relabel Sum.inr) (loaded xs n) t R :=
    htRun.relabel_to Sum.inr Sum.inr_injective (loaded xs n) R (by intro k;rfl) (by intro k;rfl) (by
      intro l hl;cases l with
      | inl i => rfl
      | inr k => exact False.elim (hl k rfl))
  have H3 := finish_run xs qr.1 qr.2 d rem n ⟨hql,hrl,hdl⟩
  have H := Run.seq _ _ _ _ _ _ _ H1 (Run.seq _ _ _ _ _ _ _ H2 H3)
  refine ⟨30*n+13+t,if rem then qr.2.reverse else qr.1.reverse,?_,?_,?_,?_⟩
  · have hys : ys.length=n := hs 0
    rw [hys] at ht
    nlinarith
  · cases rem <;> simp [hql,hrl]
  · cases rem <;> simp only [Bool.false_eq_true,↓reduceIte,List.reverse_reverse] <;> assumption
  · convert H using 1 <;> first | rfl | omega
end DivideOperator

def divide (rem : Bool) : Realizer
    (fun vs : Fin 2 → ℕ => if rem then vs 0%vs 1 else vs 0/vs 1)
    (fun n vs => 0<vs 1 ∧ 2*vs 1≤2^n) where
  W := Fin 8
  finiteW := inferInstance
  eqW := inferInstance
  out := DivideOperator.chosen rem
  program := DivideOperator.program rem
  coefficient := 101
  spec := by
    intro n hn xs hs hp
    exact DivideOperator.program_correct xs n hn hs hp.1 hp.2 rem

end SourceBurnside.Structured.Device

end OAI
