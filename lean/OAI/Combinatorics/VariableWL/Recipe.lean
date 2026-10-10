import OAI.Combinatorics.VariableWL.NumericRefinement

namespace OAI

namespace VariableWL.Computation.Stack.Procedure
open Code
variable {k : ℕ}
 theorem length_fast (a o : Fin (k+1)) :
    Realizes (fun s : Stores k=>Function.update s o (List.replicate (s a).length true))
      (fun s=>20*((s a).length+1)+3*(s o).length) := by
  let a' := front k 1 a
  let o' := front k 1 o
  let q := aux k
  have hf := seq (lengthAdd a' q (front_ne_aux a)) (seq (copy q o') (clear q))
  apply localRegisters 1 hf
  · intro s
    dsimp only [Function.comp_def,a',o',q]
    simp only [extend_front',extend_aux,List.append_nil,Function.update_self]
    rw [Function.update_comm (front_ne_aux o),Function.update_idem,clear_aux,extend_update]
  · intro s
    dsimp only [Function.comp_def,a',o',q]
    simp only [extend_front',extend_aux,List.append_nil,Function.update_self,
      Function.update_of_ne (front_ne_aux o),Function.update_of_ne (aux_ne_front o),List.length_replicate]
    omega

 theorem add_fast (a b o : Fin (k+1)) :
    Realizes (fun s : Stores k=>Function.update s o (List.replicate ((s a).length+(s b).length) true))
      (fun s=>20*((s a).length+(s b).length+1)+3*(s o).length) := by
  let a' := front k 1 a
  let b' := front k 1 b
  let o' := front k 1 o
  let q := aux k
  have hf := seq (lengthAdd b' q (front_ne_aux b))
    (seq (lengthAdd a' q (front_ne_aux a)) (seq (copy q o') (clear q)))
  apply localRegisters 1 hf
  · intro s
    dsimp only [Function.comp_def,a',b',o',q]
    simp only [extend_front',extend_aux,List.append_nil,Function.update_self,
      Function.update_of_ne (front_ne_aux a),Function.update_idem,←List.replicate_add]
    rw [Function.update_comm (front_ne_aux o),Function.update_idem,clear_aux,extend_update]
  · intro s
    dsimp only [Function.comp_def,a',b',o',q]
    simp only [extend_front',extend_aux,List.append_nil,Function.update_self,
      Function.update_of_ne (front_ne_aux a),Function.update_of_ne (front_ne_aux o),
      Function.update_of_ne (aux_ne_front o),List.length_append,List.length_replicate]
    omega

 theorem subtract_fast (a b o : Fin (k+1)) :
    Realizes (fun s : Stores k=>Function.update s o (List.replicate ((s a).length-(s b).length) true))
      (fun s=>20*((s a).length+(s b).length+1)+3*(s o).length) := by
  let a' := front k 1 a
  let b' := front k 1 b
  let o' := front k 1 o
  let q := aux k
  have hf := seq (lengthAdd a' q (front_ne_aux a))
    (seq (countedPop b' q) (seq (copy q o') (clear q)))
  apply localRegisters 1 hf
  · intro s
    dsimp only [Function.comp_def,a',b',o',q]
    simp only [extend_front',extend_aux,List.append_nil,Function.update_self,
      Function.update_of_ne (front_ne_aux b),Function.update_idem,List.drop_replicate]
    rw [Function.update_comm (front_ne_aux o),Function.update_idem,clear_aux,extend_update]
  · intro s
    dsimp only [Function.comp_def,a',b',o',q]
    simp only [extend_front',extend_aux,List.append_nil,Function.update_self,
      Function.update_of_ne (front_ne_aux b),Function.update_of_ne (front_ne_aux o),
      Function.update_of_ne (aux_ne_front o),List.length_drop,List.length_replicate]
    omega

 theorem reverse (a o : Fin (k+1)) :
    Realizes (fun s : Stores k=>Function.update s o (s a).reverse)
      (fun s=>20*((s a).length+1)+3*(s o).length) := by
  let a' := front k 1 a
  let o' := front k 1 o
  let q := aux k
  have hf := seq (reverseCopy a' q (front_ne_aux a) id) (seq (copy q o') (clear q))
  apply localRegisters 1 hf
  · intro s
    dsimp only [Function.comp_def,a',o',q]
    simp only [extend_front',extend_aux,List.append_nil,List.map_id_fun,id_eq,Function.update_self]
    rw [Function.update_comm (front_ne_aux o),Function.update_idem,clear_aux,extend_update]
  · intro s
    dsimp only [Function.comp_def,a',o',q]
    simp only [extend_front',extend_aux,List.append_nil,List.map_id_fun,id_eq,Function.update_self,
      Function.update_of_ne (front_ne_aux o),Function.update_of_ne (aux_ne_front o),List.length_reverse]
    omega

 theorem append (a b o : Fin (k+1)) :
    Realizes (fun s : Stores k=>Function.update s o (s a++s b))
      (fun s=>20*((s a).length+(s b).length+1)+3*(s o).length) := by
  let a' := front k 1 a
  let b' := front k 1 b
  let o' := front k 1 o
  let q := aux k
  have hf := seq (reverseCopy a' q (front_ne_aux a) id)
    (seq (copy b' o') (seq (reverseCopy q o' (aux_ne_front o) id) (clear q)))
  apply localRegisters 1 hf
  · intro s
    dsimp only [Function.comp_def,a',b',o',q]
    simp only [extend_front',extend_aux,List.append_nil,List.map_id_fun,id_eq,Function.update_self,
      Function.update_of_ne (front_ne_aux b),Function.update_of_ne (aux_ne_front o),List.reverse_reverse,
      Function.update_idem]
    rw [Function.update_comm (front_ne_aux o),Function.update_idem,clear_aux,extend_update]
  · intro s
    dsimp only [Function.comp_def,a',b',o',q]
    simp only [extend_front',extend_aux,List.append_nil,List.map_id_fun,id_eq,Function.update_self,
      Function.update_of_ne (front_ne_aux b),Function.update_of_ne (front_ne_aux o),
      Function.update_of_ne (aux_ne_front o),List.length_reverse]
    omega

 theorem drop (a ix o : Fin (k+1)) :
    Realizes (fun s : Stores k=>Function.update s o ((s a).drop (s ix).length))
      (fun s=>24*((s a).length+1)+11*(s ix).length+3*(s o).length) := by
  let a' := front k 1 a
  let i' := front k 1 ix
  let o' := front k 1 o
  let q := aux k
  have hf := seq (copy a' q) (seq (countedPop i' q) (seq (copy q o') (clear q)))
  apply localRegisters 1 hf
  · intro s
    dsimp only [Function.comp_def,a',i',o',q]
    simp only [extend_front',Function.update_self,Function.update_of_ne (front_ne_aux ix),
      Function.update_idem]
    rw [Function.update_comm (front_ne_aux o),Function.update_idem,clear_aux,extend_update]
  · intro s
    dsimp only [Function.comp_def,a',i',o',q]
    simp only [extend_front',extend_aux,Function.update_self,Function.update_of_ne (front_ne_aux ix),
      Function.update_of_ne (front_ne_aux o),Function.update_of_ne (aux_ne_front o),List.length_drop,List.length_nil]
    omega

end VariableWL.Computation.Stack.Procedure

namespace VariableWL.Computation.Stack.Recipe
open Procedure
abbrev Env (n : ℕ) := Fin n → Word

def cons {n : ℕ} (w : Word) (v : Env n) : Env (n+1) := Fin.cons w v

structure Certified (n : ℕ) where
  value : Env n → Word
  time : Env n → ℕ
  compiled : ∀ (k : ℕ) (ρ : Fin n → Fin (k+1)) (o : Fin (k+1)),
    Realizes (fun s : Stores k=>Function.update s o (value (s ∘ ρ)))
      (fun s=>time (s ∘ ρ)+3*(s o).length)

variable {n m : ℕ}

def reindex (P : Certified n) (φ : Fin n → Fin m) : Certified m where
  value := fun v=>P.value (v ∘ φ)
  time := fun v=>P.time (v ∘ φ)
  compiled k ρ o := P.compiled k (ρ ∘ φ) o

def input (i : Fin n) : Certified n where
  value := fun v=>v i
  time := fun v=>9*(v i).length+3
  compiled k ρ o := by
    simpa only [Function.comp_apply,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using copy (ρ i) o

def literal (w : Word) : Certified n where
  value := fun _=>w
  time := fun _=>1+2*w.length
  compiled k ρ o := by
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using constant o w

 theorem env_front (k : ℕ) (ρ : Fin n → Fin (k+1)) (s : Stores k) :
    extend 1 s ∘ (front k 1 ∘ ρ)=s ∘ ρ := by
  funext i
  exact extend_front' 1 s (ρ i)

 theorem env_temp (k : ℕ) (ρ : Fin n → Fin (k+1)) (s : Stores k) (w : Word) :
    Function.update (extend 1 s) (aux k) w ∘ (front k 1 ∘ ρ)=s ∘ ρ := by
  funext i
  simp only [Function.comp_apply,Function.update_of_ne (front_ne_aux (ρ i)),extend_front']

 theorem env_cons (k : ℕ) (ρ : Fin n → Fin (k+1)) (s : Stores k) (w : Word) :
    Function.update (extend 1 s) (aux k) w ∘ Fin.cons (aux k) (front k 1 ∘ ρ)=cons w (s ∘ ρ) := by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · simp only [Function.comp_apply,Fin.cons_zero,Function.update_self,cons]
  · simp only [Function.comp_apply,Fin.cons_succ,Function.update_of_ne (front_ne_aux (ρ j)),
      extend_front',cons]

def bind (P : Certified n) (Q : Certified (n+1)) : Certified n where
  value := fun v=>Q.value (cons (P.value v) v)
  time := fun v=>P.time v+Q.time (cons (P.value v) v)+3*(P.value v).length+2
  compiled k ρ o := by
    let ρ' := front k 1 ∘ ρ
    let o' := front k 1 o
    let q := aux k
    have hf := seq (P.compiled (k+1) ρ' q)
      (seq (Q.compiled (k+1) (Fin.cons q ρ') o') (clear q))
    apply localRegisters 1 hf
    · intro s
      dsimp only [Function.comp_def,ρ',o',q]
      rw [show (fun x => extend 1 s (front k 1 (ρ x)))=s ∘ ρ by exact env_front k ρ s]
      have hc := env_cons k ρ s (P.value (s ∘ ρ))
      dsimp only [Function.comp_def] at hc
      dsimp only [Function.comp_def]
      rw [hc]
      rw [Function.update_comm (front_ne_aux o),Function.update_idem,clear_aux,extend_update]
    · intro s
      dsimp only [Function.comp_def,ρ',o',q]
      rw [show (fun x => extend 1 s (front k 1 (ρ x)))=s ∘ ρ by exact env_front k ρ s]
      have hc := env_cons k ρ s (P.value (s ∘ ρ))
      dsimp only [Function.comp_def] at hc
      dsimp only [Function.comp_def]
      rw [hc]
      simp only [extend_aux,List.length_nil,Nat.mul_zero,Nat.add_zero,
        Function.update_of_ne (front_ne_aux o),Function.update_of_ne (aux_ne_front o),
        Function.update_self,extend_front']
      omega

def headBranch (p : (Fin n → Option Bool) → Bool) (P Q : Certified n) : Certified n where
  value := fun v=>if p (fun i=>(v i).head?) then P.value v else Q.value v
  time := fun v=>(if p (fun i=>(v i).head?) then P.time v else Q.time v)+1
  compiled k ρ o := by
    have h := branch (fun h=>p (h ∘ ρ)) (P.compiled k ρ o) (Q.compiled k ρ o)
    have he : (fun s : Stores k => if p (heads s ∘ ρ) then Function.update s o (P.value (s ∘ ρ))
        else Function.update s o (Q.value (s ∘ ρ)))=
        (fun s : Stores k => Function.update s o (if p (fun i=>(s (ρ i)).head?) then P.value (s ∘ ρ) else Q.value (s ∘ ρ))) := by
      funext s
      change (if p (fun i=>(s (ρ i)).head?) then _ else _)=_
      split <;> rfl
    rw [he] at h
    apply monotone h
    intro s
    change (if p (fun i=>(s (ρ i)).head?) then P.time (s ∘ ρ)+3*(s o).length
      else Q.time (s ∘ ρ)+3*(s o).length)+1 ≤ _
    dsimp only [Function.comp_apply]
    split_ifs <;> omega

def test (p : (Fin n → Option Bool) → Bool) : Certified n :=
  headBranch p (literal [true]) (literal [false])

 theorem test_value (p : (Fin n → Option Bool) → Bool) (v : Env n) :
    (test p).value v=[p (fun i=>(v i).head?)] := by
  simp only [test,headBranch,literal]
  split <;> rename_i h <;> simp_all

def length (i : Fin n) : Certified n where
  value := fun v=>List.replicate (v i).length true
  time := fun v=>20*((v i).length+1)
  compiled k ρ o := by simpa only [Function.comp_apply] using length_fast (ρ i) o

def add (i j : Fin n) : Certified n where
  value := fun v=>List.replicate ((v i).length+(v j).length) true
  time := fun v=>20*((v i).length+(v j).length+1)
  compiled k ρ o := by simpa only [Function.comp_apply] using add_fast (ρ i) (ρ j) o

def subtract (i j : Fin n) : Certified n where
  value := fun v=>List.replicate ((v i).length-(v j).length) true
  time := fun v=>20*((v i).length+(v j).length+1)
  compiled k ρ o := by simpa only [Function.comp_apply] using subtract_fast (ρ i) (ρ j) o

def multiply (i j : Fin n) : Certified n where
  value := fun v=>List.replicate ((v i).length*(v j).length) true
  time := fun v=>20*((v i).length+1)*((v j).length+1)+10
  compiled k ρ o := by
    simpa only [Function.comp_apply,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using Procedure.multiply (ρ i) (ρ j) o

def reverse (i : Fin n) : Certified n where
  value := fun v=>(v i).reverse
  time := fun v=>20*((v i).length+1)
  compiled k ρ o := by simpa only [Function.comp_apply] using Procedure.reverse (ρ i) o

def append (i j : Fin n) : Certified n where
  value := fun v=>v i++v j
  time := fun v=>20*((v i).length+(v j).length+1)
  compiled k ρ o := by simpa only [Function.comp_apply] using Procedure.append (ρ i) (ρ j) o

def drop (i j : Fin n) : Certified n where
  value := fun v=>(v i).drop (v j).length
  time := fun v=>24*((v i).length+1)+11*(v j).length
  compiled k ρ o := by simpa only [Function.comp_apply] using Procedure.drop (ρ i) (ρ j) o

def lookup (i j : Fin n) : Certified n where
  value := fun v=>[(v i).getD (v j).length false]
  time := fun v=>12*(v i).length+11*(v j).length+12
  compiled k ρ o := by
    simpa only [Function.comp_apply,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using Procedure.lookup (ρ i) (ρ j) o

end VariableWL.Computation.Stack.Recipe

namespace VariableWL.Computation.Stack.Recipe
open Procedure
variable {n : ℕ}

 def foldValue (Q : Certified (n+2)) (v : Env n) (w : Word) : ℕ → Word
  | 0 => w
  | j+1 => Q.value (cons (foldValue Q v w j) (cons (List.replicate j true) v))

 def foldTime (Q : Certified (n+2)) (v : Env n) (w : Word) (j : ℕ) : ℕ :=
  Q.time (cons (foldValue Q v w j) (cons (List.replicate j true) v))+
    3*(foldValue Q v w j).length+2

noncomputable def frame {k : ℕ} (s : Stores k) (j : ℕ) (w : Word) : Stores (k+2) :=
  Function.update (BoundedLoop.state k s j) (BoundedLoop.scratch k) w

 @[simp] theorem frame_front {k : ℕ} (s : Stores k) (j : ℕ) (w : Word) (i : Fin (k+1)) :
    frame s j w (BoundedLoop.embed k i)=s i := by
  rw [frame,Function.update_of_ne (BoundedLoop.scratch_ne k i),BoundedLoop.state_embed]

 @[simp] theorem frame_index {k : ℕ} (s : Stores k) (j : ℕ) (w : Word) :
    frame s j w (BoundedLoop.counter k)=List.replicate j true := by
  rw [frame,Function.update_of_ne (BoundedLoop.counter_scratch k),BoundedLoop.state_counter]

 @[simp] theorem frame_acc {k : ℕ} (s : Stores k) (j : ℕ) (w : Word) :
    frame s j w (BoundedLoop.scratch k)=w := Function.update_self ..

 def foldInputs (k : ℕ) (ρ : Fin n → Fin (k+1)) : Fin (n+2) → Fin (k+2+1) :=
  Fin.cons (BoundedLoop.scratch k) (Fin.cons (BoundedLoop.counter k) (BoundedLoop.embed k ∘ ρ))

 theorem frame_env {k : ℕ} (ρ : Fin n → Fin (k+1)) (s : Stores k) (j : ℕ) (w : Word) :
    frame s j w ∘ foldInputs k ρ=cons w (cons (List.replicate j true) (s ∘ ρ)) := by
  funext i
  refine Fin.cases ?_ (fun i=>Fin.cases ?_ (fun i=>?_) i) i
  · simp only [foldInputs,Function.comp_apply,Fin.cons_zero,frame_acc,cons]
  · simp only [foldInputs,Function.comp_apply,Fin.cons_succ,Fin.cons_zero,frame_index,cons]
  · simp only [foldInputs,Function.comp_apply,Fin.cons_succ,frame_front,cons]

 theorem frame_initial {k : ℕ} (s : Stores k) (w : Word) :
    Function.update (extend 2 s) (BoundedLoop.scratch k) w=frame s 0 w := by
  rw [←state_base]
  rfl

 theorem frame_step {k : ℕ} (s : Stores k) (j : ℕ) (w v : Word) :
    Function.update (Function.update (frame s j w) (BoundedLoop.scratch k) v)
      (BoundedLoop.counter k)
      (true::Function.update (frame s j w) (BoundedLoop.scratch k) v (BoundedLoop.counter k))=
    frame s (j+1) v := by
  rw [Function.update_of_ne (BoundedLoop.counter_scratch k),frame_index,←List.replicate_succ]
  unfold frame
  rw [Function.update_idem,Function.update_comm (Ne.symm (BoundedLoop.counter_scratch k)),BoundedLoop.update_counter]

 theorem frame_finish {k : ℕ} (s : Stores k) (j : ℕ) (w : Word) (o : Fin (k+1)) :
    Function.update (Function.update (Function.update (frame s j w) (BoundedLoop.embed k o) w)
      (BoundedLoop.scratch k) []) (BoundedLoop.counter k) []=
      extend 2 (Function.update s o w) := by
  funext z
  rcases BoundedLoop.cases_index k z with ⟨i,rfl⟩|rfl|rfl
  · have ht : extend 2 (Function.update s o w) (BoundedLoop.embed k i)=Function.update s o w i :=
      extend_front 2 _ i
    rw [ht,Function.update_of_ne (BoundedLoop.counter_ne k i),
      Function.update_of_ne (BoundedLoop.scratch_ne k i)]
    by_cases hi : i=o
    · subst i; simp only [Function.update_self]
    · rw [Function.update_of_ne (fun h=>hi ((BoundedLoop.embed k).injective h)),
        Function.update_of_ne hi,frame_front]
  · rw [Function.update_self,extend_back _ _ _ (by rfl)]
  · rw [Function.update_of_ne (Ne.symm (BoundedLoop.counter_scratch k)),Function.update_self,
      extend_back _ _ _ (by change k+1≤k+2; omega)]

 def foldBody {k : ℕ} (Q : Certified (n+2)) (ρ : Fin n → Fin (k+1)) (s : Stores (k+2)) : Stores (k+2) :=
  let t := Function.update s (BoundedLoop.scratch k) (Q.value (s ∘ foldInputs k ρ))
  Function.update t (BoundedLoop.counter k) (true::t (BoundedLoop.counter k))

 theorem iterate_foldBody {k : ℕ} (Q : Certified (n+2)) (ρ : Fin n → Fin (k+1))
    (s : Stores k) (w : Word) (j : ℕ) :
    ((foldBody Q ρ)^[j]) (frame s 0 w)=frame s j (foldValue Q (s ∘ ρ) w j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply',ih]
    unfold foldBody
    rw [frame_env,frame_step]
    rfl

 def fold (b z : Fin n) (Q : Certified (n+2)) : Certified n where
  value := fun v=>foldValue Q v (v z) (v b).length
  time := fun v=>9*(v z).length+9*(v b).length+
    BoundedLoop.total (v b).length (foldTime Q v (v z))+
    12*(foldValue Q v (v z) (v b).length).length+20
  compiled k ρ o := by
    let q := BoundedLoop.counter k
    let a := BoundedLoop.scratch k
    let ρ' := BoundedLoop.embed k ∘ ρ
    let o' := BoundedLoop.embed k o
    have hb := seq (Q.compiled (k+2) (foldInputs k ρ) a) (push q true)
    have hf := seq (copy (ρ' z) a) (seq (countedLoop (ρ' b) hb)
      (seq (copy a o') (seq (clear a) (clear q))))
    apply localRegisters 2 hf
    · intro s
      dsimp only [Function.comp_def,ρ',o',a,q]
      rw [show extend 2 s (BoundedLoop.embed k (ρ z))=s (ρ z) from extend_front 2 s (ρ z)]
      rw [frame_initial]
      change Function.update (Function.update (Function.update
        (((foldBody Q ρ)^[(frame s 0 (s (ρ z)) (BoundedLoop.embed k (ρ b))).length])
          (frame s 0 (s (ρ z)))) (BoundedLoop.embed k o)
        ((((foldBody Q ρ)^[(frame s 0 (s (ρ z)) (BoundedLoop.embed k (ρ b))).length])
          (frame s 0 (s (ρ z)))) (BoundedLoop.scratch k)))
        (BoundedLoop.scratch k) []) (BoundedLoop.counter k) []=_
      rw [frame_front,iterate_foldBody,frame_acc,frame_finish]
      rfl
    · intro s
      dsimp only [Function.comp_def,ρ',o',a,q]
      rw [show extend 2 s (BoundedLoop.embed k (ρ z))=s (ρ z) from extend_front 2 s (ρ z)]
      rw [show extend 2 s (BoundedLoop.scratch k)=[] from extend_back 2 s _ (by change k+1≤k+2; omega)]
      rw [frame_initial,frame_front]
      have hj (j : ℕ) :
          ((fun t : Stores (k+2) => Function.update
            (Function.update t (BoundedLoop.scratch k) (Q.value (fun x=>t (foldInputs k ρ x))))
            (BoundedLoop.counter k) (true::t (BoundedLoop.counter k)))^[j]) (frame s 0 (s (ρ z)))=
          frame s j (foldValue Q (s ∘ ρ) (s (ρ z)) j) := by
        have heq : foldBody Q ρ=(fun t : Stores (k+2) => Function.update
            (Function.update t (BoundedLoop.scratch k) (Q.value (fun x=>t (foldInputs k ρ x))))
            (BoundedLoop.counter k) (true::t (BoundedLoop.counter k))) := by
          funext t
          unfold foldBody
          simp only [Function.comp_def,Function.update_of_ne (BoundedLoop.counter_scratch k)]
        rw [←heq]
        exact iterate_foldBody Q ρ s (s (ρ z)) j
      have henv (j : ℕ) : (fun x=>frame s j (foldValue Q (s ∘ ρ) (s (ρ z)) j) (foldInputs k ρ x))=
          cons (foldValue Q (s ∘ ρ) (s (ρ z)) j) (cons (List.replicate j true) (s ∘ ρ)) :=
        frame_env ρ s j _
      simp only [hj,henv,frame_acc,frame_front,List.length_nil,Nat.mul_zero,Nat.add_zero,
        Function.update_of_ne (Ne.symm (BoundedLoop.scratch_ne k o)),
        Function.update_of_ne (Ne.symm (BoundedLoop.counter_ne k o)),
        Function.update_of_ne (BoundedLoop.counter_scratch k),frame_index,List.length_replicate]
      have he : (fun j=>Q.time (cons (foldValue Q (s ∘ ρ) (s (ρ z)) j)
        (cons (List.replicate j true) (s ∘ ρ)))+3*(foldValue Q (s ∘ ρ) (s (ρ z)) j).length+1+1)=
        foldTime Q (s ∘ ρ) (s (ρ z)) := by funext j; simp only [foldTime]
      rw [he]
      simp only [Function.comp_def]
      omega

end VariableWL.Computation.Stack.Recipe

end OAI
