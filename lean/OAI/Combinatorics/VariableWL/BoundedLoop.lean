import OAI.Combinatorics.VariableWL.BinaryMachine

namespace OAI

namespace VariableWL.Computation.Stack.Code
variable {k l : ℕ}

noncomputable def put (e : Fin (k+1) ↪ Fin (l+1)) (s : Stores k) (t : Stores l) : Stores l := by
  classical
  exact fun j => if h : ∃ i, e i=j then s h.choose else t j

 theorem put_apply (e : Fin (k+1) ↪ Fin (l+1)) (s : Stores k) (t : Stores l) (i : Fin (k+1)) :
    put e s t (e i)=s i := by
  classical
  unfold put
  rw [dite_eq_left ⟨i,rfl⟩]
  congr 1
  exact e.injective (Exists.choose_spec (show ∃ a, e a=e i from ⟨i,rfl⟩))

 theorem put_outside (e : Fin (k+1) ↪ Fin (l+1)) (s : Stores k) (t : Stores l) {j : Fin (l+1)}
    (h : ¬∃ i, e i=j) : put e s t j=t j := by
  classical
  exact dite_eq_right h

 theorem put_self (e : Fin (k+1) ↪ Fin (l+1)) (s : Stores l) : put e (s ∘ e) s=s := by
  funext j
  by_cases h : ∃ i, e i=j
  · obtain ⟨i,rfl⟩ := h
    exact put_apply e (s ∘ e) s i
  · exact put_outside e (s ∘ e) s h

 theorem put_put (e : Fin (k+1) ↪ Fin (l+1)) (s s' : Stores k) (t : Stores l) :
    put e s' (put e s t)=put e s' t := by
  funext j
  by_cases h : ∃ i, e i=j
  · obtain ⟨i,rfl⟩ := h
    rw [put_apply,put_apply]
  · rw [put_outside e s' _ h,put_outside e s _ h,put_outside e s' _ h]

noncomputable def liftAction (e : Fin (k+1) ↪ Fin (l+1)) (a : Actions k) : Actions l := by
  classical
  exact fun j => if h : ∃ i, e i=j then a h.choose else .keep

 theorem liftAction_apply (e : Fin (k+1) ↪ Fin (l+1)) (a : Actions k) (i : Fin (k+1)) :
    liftAction e a (e i)=a i := by
  classical
  unfold liftAction
  rw [dite_eq_left ⟨i,rfl⟩]
  congr 1
  exact e.injective (Exists.choose_spec (show ∃ b, e b=e i from ⟨i,rfl⟩))

 theorem liftAction_outside (e : Fin (k+1) ↪ Fin (l+1)) (a : Actions k) {j : Fin (l+1)}
    (h : ¬∃ i, e i=j) : liftAction e a j=.keep := by
  classical
  exact dite_eq_right h

 theorem execute_liftAction (e : Fin (k+1) ↪ Fin (l+1)) (a : Actions k) (s : Stores k) (t : Stores l) :
    execute (liftAction e a) (put e s t)=put e (execute a s) t := by
  funext j
  by_cases h : ∃ i, e i=j
  · obtain ⟨i,rfl⟩ := h
    simp only [execute,liftAction_apply,put_apply]
  · simp only [execute,liftAction_outside e a h,put_outside e s t h,
      put_outside e (execute a s) t h,Action.apply]

 theorem heads_put (e : Fin (k+1) ↪ Fin (l+1)) (s : Stores k) (t : Stores l) :
    heads (put e s t) ∘ e=heads s := by
  funext i
  simp only [Function.comp_apply,heads,put_apply]

noncomputable def rename (e : Fin (k+1) ↪ Fin (l+1)) : Code k → Code l
  | .skip => .skip
  | .action a => .action fun h => liftAction e (a (h ∘ e))
  | .seq a b => .seq (rename e a) (rename e b)
  | .branch p a b => .branch (fun h => p (h ∘ e)) (rename e a) (rename e b)
  | .loop p a => .loop (fun h => p (h ∘ e)) (rename e a)

 theorem eval_rename (e : Fin (k+1) ↪ Fin (l+1)) {C : Code k} {s s' : Stores k} {n : ℕ}
    (h : Eval C s n s') (t : Stores l) : Eval (rename e C) (put e s t) n (put e s' t) := by
  induction h with
  | skip s => exact Eval.skip _
  | action a s =>
    have hh := Eval.action (fun h : Heads l => liftAction e (a (h ∘ e))) (put e s t)
    rw [heads_put,execute_liftAction] at hh
    exact hh
  | seq _ _ ia ib => exact Eval.seq ia ib
  | @branch_true p a b s u n hp ha ih =>
    exact Eval.branch_true (by simpa only [heads_put] using hp) ih
  | @branch_false p a b s u n hp ha ih =>
    exact Eval.branch_false (by simpa only [heads_put] using hp) ih
  | loop_false hp => exact Eval.loop_false (by simpa only [heads_put] using hp)
  | @loop_true p a s u v n m hp ha hb ia ib =>
    exact Eval.loop_true (by simpa only [heads_put] using hp) ia ib

 theorem eval_rename_from (e : Fin (k+1) ↪ Fin (l+1)) {C : Code k} {s' : Stores k} {n : ℕ}
    (t : Stores l) (h : Eval C (t ∘ e) n s') : Eval (rename e C) t n (put e s' t) := by
  simpa only [put_self] using eval_rename e h t

end VariableWL.Computation.Stack.Code

namespace VariableWL.Computation.Stack.BoundedLoop
open Code
variable (k : ℕ)

def embed : Fin (k+1) ↪ Fin (k+3) := Fin.castAddEmb 2
def counter : Fin (k+3) := ⟨k+1,by omega⟩
def scratch : Fin (k+3) := ⟨k+2,by omega⟩

 theorem counter_ne (i : Fin (k+1)) : embed k i≠counter k := by
  intro h
  have := congrArg Fin.val h
  change i.val=k+1 at this
  omega

 theorem scratch_ne (i : Fin (k+1)) : embed k i≠scratch k := by
  intro h
  have := congrArg Fin.val h
  change i.val=k+2 at this
  omega

 theorem counter_scratch : counter k≠scratch k := by
  intro h
  have := congrArg Fin.val h
  simp only [counter,scratch] at this
  omega

noncomputable def state (s : Stores k) (n : ℕ) : Stores (k+2) :=
  put (embed k) s (fun j => if j=counter k then List.replicate n true else [])

@[simp] theorem state_embed (s : Stores k) (n : ℕ) (i : Fin (k+1)) :
    state k s n (embed k i)=s i := put_apply _ _ _ _

@[simp] theorem state_counter (s : Stores k) (n : ℕ) :
    state k s n (counter k)=List.replicate n true := by
  rw [state,put_outside]
  · simp only [ite_true]
  · rintro ⟨i,hi⟩
    exact counter_ne k i hi

@[simp] theorem state_scratch (s : Stores k) (n : ℕ) :
    state k s n (scratch k)=[] := by
  rw [state,put_outside]
  · simp only [Ne.symm (counter_scratch k),ite_false]
  · rintro ⟨i,hi⟩
    exact scratch_ne k i hi

 theorem cases_index (j : Fin (k+3)) :
    (∃ i : Fin (k+1), embed k i=j) ∨ j=counter k ∨ j=scratch k := by
  by_cases h : j.val<k+1
  · left
    exact ⟨⟨j.val,h⟩,Fin.ext rfl⟩
  · right
    have : j.val=k+1 ∨ j.val=k+2 := by omega
    rcases this with h|h
    · exact .inl (Fin.ext h)
    · exact .inr (Fin.ext h)

 theorem update_counter (s : Stores k) (n m : ℕ) :
    Function.update (state k s n) (counter k) (List.replicate m true)=state k s m := by
  funext j
  rcases cases_index k j with ⟨i,rfl⟩|rfl|rfl
  · simp only [Function.update_of_ne (counter_ne k i),state_embed]
  · simp only [Function.update_self,state_counter]
  · simp only [Function.update_of_ne (Ne.symm (counter_scratch k)),state_scratch]

 theorem put_state (s t : Stores k) (n : ℕ) : put (embed k) t (state k s n)=state k t n := by
  exact put_put _ _ _ _

noncomputable def loopBody (a : Code k) : Code (k+2) := .seq (pop (counter k)) (rename (embed k) a)
noncomputable def loop (a : Code k) : Code (k+2) := .loop (fun h => (h (counter k)).isSome) (loopBody k a)
noncomputable def program (i : Fin (k+1)) (a : Code k) : Code (k+2) :=
  .seq (duplicate (embed k i) (scratch k) (counter k) (fun _ => true)) (loop k a)

 theorem eval_body {a : Code k} {s t : Stores k} {c : ℕ} (h : Eval a s c t) (n : ℕ) :
    Eval (loopBody k a) (state k s (n+1)) (c+2) (state k t n) := by
  have hp := eval_pop (counter k) (state k s (n+1))
  rw [state_counter,List.replicate_succ,List.tail_cons,update_counter] at hp
  have hb := eval_rename (embed k) h (state k s n)
  rw [put_state,put_state] at hb
  have he := Eval.seq hp hb
  have hn : c+2=1+1+c := by omega
  rw [hn]
  exact he

def total : ℕ → (ℕ → ℕ) → ℕ
  | 0,_ => 0
  | n+1,T => T 0+4+total n (fun j => T (j+1))

 theorem eval_loop (a : Code k) (n : ℕ) (S : ℕ → Stores k) (T : ℕ → ℕ)
    (h : ∀ j<n, Eval a (S j) (T j) (S (j+1))) :
    Eval (loop k a) (state k (S 0) n) (total n T) (state k (S n) 0) := by
  induction n generalizing S T with
  | zero => exact Eval.loop_false (by simp only [heads,state_counter,List.replicate_zero,List.head?_nil,Option.isSome_none])
  | succ n ih =>
    have h0 := eval_body k (h 0 (by omega)) n
    have ht := ih (fun j => S (j+1)) (fun j => T (j+1)) (by intro j hj; exact h (j+1) (by omega))
    have he := Eval.loop_true (p := fun h => (h (counter k)).isSome)
      (by simp [heads,List.replicate_succ]) h0 ht
    have hn : total (n+1) T=(T 0+2)+2+total n (fun j => T (j+1)) := by simp only [total]
    rw [hn]
    exact he

 theorem eval_program (i : Fin (k+1)) (a : Code k) (S : ℕ → Stores k) (T : ℕ → ℕ)
    (h : ∀ j<(S 0 i).length, Eval a (S j) (T j) (S (j+1))) :
    Eval (program k i a) (state k (S 0) 0)
      (6*(S 0 i).length+2+total (S 0 i).length T) (state k (S (S 0 i).length) 0) := by
  have hd := eval_length_add (embed k i) (scratch k) (counter k) (scratch_ne k i)
    (counter_ne k i) (Ne.symm (counter_scratch k)) (state k (S 0) 0)
    (state_scratch k _ _) 0 (state_counter k _ _)
  simp only [state_embed,Nat.add_zero,update_counter] at hd
  have he := Eval.seq hd (eval_loop k a _ S T h)
  have hn : 6*(S 0 i).length+2+total (S 0 i).length T=
      (6*(S 0 i).length+1)+1+total (S 0 i).length T := by omega
  rw [hn]
  exact he

 theorem total_bound (n B : ℕ) (T : ℕ → ℕ) (h : ∀ j<n, T j≤B) : total n T≤(B+4)*n := by
  induction n generalizing T with
  | zero => simp [total]
  | succ n ih =>
    have hi := ih (fun j => T (j+1)) (by intro j hj; exact h (j+1) (by omega))
    have h0 := h 0 (by omega)
    simp only [total]
    nlinarith

 theorem program_bound (n B : ℕ) (T : ℕ → ℕ) (h : ∀ j<n, T j≤B) :
    6*n+2+total n T≤(B+10)*n+2 := by
  have := total_bound n B T h
  nlinarith

end VariableWL.Computation.Stack.BoundedLoop

namespace VariableWL.TupleAddress

def encode {n k : ℕ} (v : Fin k → Fin n) : ℕ := (finFunctionFinEquiv v).val

def digit (n a i : ℕ) : ℕ := a/n^i%n

def replace (n a i z : ℕ) : ℕ := a-digit n a i*n^i+z*n^i

 theorem encode_lt {n k : ℕ} (v : Fin k → Fin n) : encode v<n^k :=
  (finFunctionFinEquiv v).isLt

 theorem digit_encode {n k : ℕ} (v : Fin k → Fin n) (i : Fin k) :
    digit n (encode v) i.val=(v i).val := by
  have he := congrArg (fun f : Fin k → Fin n => (f i).val) (finFunctionFinEquiv.symm_apply_apply v)
  exact he

 theorem encode_sum {n k : ℕ} (v : Fin k → Fin n) :
    encode v=∑i:Fin k,(v i).val*n^i.val := rfl

 theorem encode_update {n k : ℕ} (v : Fin k → Fin n) (i : Fin k) (z : Fin n) :
    encode (Function.update v i z)=replace n (encode v) i.val z.val := by
  classical
  let rest := ∑j∈Finset.univ.erase i,(v j).val*n^j.val
  have ha : rest+(v i).val*n^i.val=encode v := by
    exact Finset.sum_erase_add _ _ (Finset.mem_univ i)
  have hb : rest+z.val*n^i.val=encode (Function.update v i z) := by
    rw [encode_sum,←Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  unfold replace
  rw [digit_encode]
  omega

 theorem digit_unpack {n k : ℕ} (a : Fin (n^k)) (i : Fin k) :
    (finFunctionFinEquiv.symm a i).val=digit n a.val i.val := rfl

 theorem encode_unpack {n k : ℕ} (a : Fin (n^k)) :
    encode (finFunctionFinEquiv.symm a)=a.val := congrArg Fin.val (finFunctionFinEquiv.apply_symm_apply a)

 theorem replace_lt {n k : ℕ} (a : Fin (n^k)) (i : Fin k) (z : Fin n) :
    replace n a.val i.val z.val<n^k := by
  rw [←encode_unpack a,←encode_update]
  exact encode_lt _

 theorem decode_replace {n k : ℕ} (a : Fin (n^k)) (i : Fin k) (z : Fin n) :
    finFunctionFinEquiv.symm (⟨replace n a.val i.val z.val,replace_lt a i z⟩ : Fin (n^k))=
      Function.update (finFunctionFinEquiv.symm a) i z := by
  apply finFunctionFinEquiv.injective
  rw [finFunctionFinEquiv.apply_symm_apply]
  apply Fin.ext
  exact (encode_update _ i z).trans (by rw [encode_unpack]) |>.symm

end VariableWL.TupleAddress

end OAI
