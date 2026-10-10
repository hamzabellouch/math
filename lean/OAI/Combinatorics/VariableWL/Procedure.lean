import OAI.Combinatorics.VariableWL.BoundedLoop

namespace OAI

namespace VariableWL.Computation.Stack.Procedure
open Code
variable {k : ℕ}

def extend (e : ℕ) (s : Stores k) : Stores (k+e) :=
  fun j => if h : j.val<k+1 then s ⟨j.val,h⟩ else []

@[simp] theorem extend_front (e : ℕ) (s : Stores k) (i : Fin (k+1)) :
    extend e s (⟨i.val,by omega⟩ : Fin (k+e+1))=s i := by
  simp only [extend, i.isLt, dite_true]

 theorem extend_back (e : ℕ) (s : Stores k) (j : Fin (k+e+1)) (h : k+1≤j.val) :
    extend e s j=[] := by simp only [extend,show ¬j.val<k+1 by omega,dite_false]

 theorem extend_zero (s : Stores k) : extend 0 s=s := by
  funext i
  exact extend_front 0 s i

def widen (k e f : ℕ) (h : e≤f) : Fin (k+e+1) ↪ Fin (k+f+1) :=
  Fin.castLEEmb (by omega)

 theorem extend_project (e f : ℕ) (h : e≤f) (s : Stores k) :
    extend f s ∘ widen k e f h=extend e s := by
  funext i
  simp only [extend,Function.comp_apply,widen,Fin.coe_castLEEmb,Fin.val_castLE]

 theorem extend_put (e f : ℕ) (h : e≤f) (s t : Stores k) :
    put (widen k e f h) (extend e t) (extend f s)=extend f t := by
  classical
  funext j
  by_cases hj : j.val<k+e+1
  · let i : Fin (k+e+1) := ⟨j.val,hj⟩
    have he : widen k e f h i=j := Fin.ext rfl
    rw [←he,put_apply]
    have hp := congrFun (extend_project e f h t) i
    exact hp.symm
  · have hout : ¬∃i, widen k e f h i=j := by
      rintro ⟨i,hi⟩
      have hv := congrArg Fin.val hi
      change i.val=j.val at hv
      omega
    rw [put_outside _ _ _ hout]
    rw [extend_back _ _ _ (by omega),extend_back _ _ _ (by omega)]

 theorem eval_widen {e f : ℕ} (h : e≤f) {C : Code (k+e)} {s t : Stores k} {n : ℕ}
    (hc : Eval C (extend e s) n (extend e t)) :
    Eval (rename (widen k e f h) C) (extend f s) n (extend f t) := by
  have he := eval_rename_from (widen k e f h) (t := extend f s)
    (by simpa only [extend_project] using hc)
  rw [extend_put] at he
  exact he

def Realizes (f : Stores k → Stores k) (T : Stores k → ℕ) : Prop :=
  ∃ e : ℕ, ∃ C : Code (k+e), ∀ s, ∃ n≤T s, Eval C (extend e s) n (extend e (f s))

 theorem monotone {f : Stores k → Stores k} {T U : Stores k → ℕ}
    (h : Realizes f T) (hTU : ∀ s, T s≤U s) : Realizes f U := by
  obtain ⟨e,C,hC⟩ := h
  refine ⟨e,C,fun s => ?_⟩
  obtain ⟨n,hn,he⟩ := hC s
  exact ⟨n,hn.trans (hTU s),he⟩

 theorem direct (C : Code k) (f : Stores k → Stores k) (T : Stores k → ℕ)
    (h : ∀s,∃n≤T s,Eval C s n (f s)) : Realizes f T := by
  refine ⟨0,C,fun s => ?_⟩
  simpa only [extend_zero] using h s

 theorem identity : Realizes (id : Stores k → Stores k) (fun _ => 0) :=
  direct .skip id (fun _ => 0) (fun s => ⟨0,le_rfl,Eval.skip s⟩)

 theorem seq {f g : Stores k → Stores k} {T U : Stores k → ℕ}
    (hf : Realizes f T) (hg : Realizes g U) :
    Realizes (g ∘ f) (fun s => T s+1+U (f s)) := by
  obtain ⟨e,A,hA⟩ := hf
  obtain ⟨f',B,hB⟩ := hg
  let a := widen k e (max e f') (Nat.le_max_left _ _)
  let b := widen k f' (max e f') (Nat.le_max_right _ _)
  refine ⟨max e f',.seq (rename a A) (rename b B),fun s => ?_⟩
  obtain ⟨n,hn,heA⟩ := hA s
  obtain ⟨m,hm,heB⟩ := hB (f s)
  exact ⟨n+1+m,by dsimp only; omega, Eval.seq (eval_widen _ heA) (eval_widen _ heB)⟩

 theorem clear (i : Fin (k+1)) :
    Realizes (fun s : Stores k => Function.update s i []) (fun s => 3*(s i).length) :=
  direct (Code.clear i) _ _ (fun s => ⟨_,le_rfl,eval_clear i s⟩)

 theorem push (i : Fin (k+1)) (b : Bool) :
    Realizes (fun s : Stores k => Function.update s i (b::s i)) (fun _ => 1) :=
  direct (Code.push i b) _ _ (fun s => ⟨_,le_rfl,eval_push i b s⟩)

 theorem pop (i : Fin (k+1)) :
    Realizes (fun s : Stores k => Function.update s i (s i).tail) (fun _ => 1) :=
  direct (Code.pop i) _ _ (fun s => ⟨_,le_rfl,eval_pop i s⟩)

 theorem action (a : Heads k → Actions k) :
    Realizes (fun s => execute (a (heads s)) s) (fun _ => 1) :=
  direct (.action a) _ _ (fun s => ⟨_,le_rfl,Eval.action a s⟩)

 theorem outputs {f : Stores k → Stores k} {T : Stores k → ℕ} (o : Fin (k+1))
    (h : Realizes f T) : ∃ M : VariableWL.Machine, ∀ w : Word,
      VariableWL.OutputsWithin M w
        (f (fun j => if j=0 then w.reverse else []) o)
        (4*(w.length+T (fun j => if j=0 then w.reverse else [])+1)) := by
  obtain ⟨e,C,hC⟩ := h
  let out : Fin (k+e+1) := ⟨o.val,by omega⟩
  refine ⟨(C.machine out).compile,fun w => ?_⟩
  let s : Stores k := fun j => if j=0 then w.reverse else []
  obtain ⟨n,hn,he⟩ := hC s
  have hs : extend e s=(fun j => if j=0 then w.reverse else []) := by
    funext j
    by_cases hj : j.val<k+1
    · simp only [extend,hj,dite_true,s]
      have hz : (⟨j.val,hj⟩ : Fin (k+1))=0 ↔ j=0 := by simp only [Fin.ext_iff,Fin.val_zero]
      simp only [hz]
    · rw [extend_back _ _ _ (by omega)]
      have hz : j≠0 := by intro hz; subst j; simp only [Fin.val_zero] at hj; omega
      simp only [hz,ite_false]
  rw [hs] at he
  have ho := eval_outputs C out w he
  rw [extend_front] at ho
  obtain ⟨t,ht,hh,hout⟩ := ho
  exact ⟨t,ht.trans (by dsimp only [s] at hn; omega),hh,hout⟩

end VariableWL.Computation.Stack.Procedure

namespace VariableWL.Computation.Stack.Procedure
open Code
variable {k : ℕ}

def front (k e : ℕ) : Fin (k+1) ↪ Fin (k+e+1) := Fin.castLEEmb (by omega)

 theorem heads_extend (e : ℕ) (s : Stores k) : heads (extend e s) ∘ front k e=heads s := by
  funext i
  change (extend e s (⟨i.val,_⟩ : Fin (k+e+1))).head?=(s i).head?
  rw [extend_front]

 theorem branch (p : Heads k → Bool) {f g : Stores k → Stores k} {T U : Stores k → ℕ}
    (hf : Realizes f T) (hg : Realizes g U) :
    Realizes (fun s => if p (heads s) then f s else g s)
      (fun s => (if p (heads s) then T s else U s)+1) := by
  obtain ⟨e,A,hA⟩ := hf
  obtain ⟨f',B,hB⟩ := hg
  let a := widen k e (max e f') (Nat.le_max_left _ _)
  let b := widen k f' (max e f') (Nat.le_max_right _ _)
  let p' : Heads (k+max e f') → Bool := fun h => p (h ∘ front k (max e f'))
  refine ⟨max e f',.branch p' (rename a A) (rename b B),fun s => ?_⟩
  have hps : p' (heads (extend (max e f') s))=p (heads s) := by change p (heads (extend (max e f') s) ∘ front k (max e f'))=p (heads s); rw [heads_extend]
  cases hp : p (heads s) with
  | false =>
    obtain ⟨n,hn,he⟩ := hB s
    simp only [hp,Bool.false_eq_true,ite_false]
    exact ⟨n+1,by omega,Eval.branch_false (hps.trans hp) (eval_widen _ he)⟩
  | true =>
    obtain ⟨n,hn,he⟩ := hA s
    simp only [hp,ite_true]
    exact ⟨n+1,by omega,Eval.branch_true (hps.trans hp) (eval_widen _ he)⟩

 theorem state_extend (e : ℕ) (s : Stores k) :
    BoundedLoop.state (k+e) (extend e s) 0=extend (e+2) s := by
  funext j
  rcases BoundedLoop.cases_index (k+e) j with ⟨i,rfl⟩|rfl|rfl
  · rw [BoundedLoop.state_embed]
    rfl
  · rw [BoundedLoop.state_counter, List.replicate_zero]
    exact (extend_back _ _ _ (by change k+1≤k+e+1; omega)).symm
  · rw [BoundedLoop.state_scratch]
    exact (extend_back _ _ _ (by change k+1≤k+e+2; omega)).symm

 theorem total_mono (n : ℕ) (A B : ℕ → ℕ) (h : ∀j<n,A j≤B j) :
    BoundedLoop.total n A≤BoundedLoop.total n B := by
  induction n generalizing A B with
  | zero => rfl
  | succ n ih =>
    have hi := ih (fun j=>A (j+1)) (fun j=>B (j+1)) (by intro j hj; exact h (j+1) (by omega))
    have h0 := h 0 (by omega)
    simp only [BoundedLoop.total]
    omega

 theorem countedLoop (i : Fin (k+1)) {f : Stores k → Stores k} {T : Stores k → ℕ}
    (hf : Realizes f T) :
    Realizes (fun s => (f^[(s i).length]) s)
      (fun s => 6*(s i).length+2+BoundedLoop.total (s i).length (fun j => T ((f^[j]) s))) := by
  classical
  obtain ⟨e,A,hA⟩ := hf
  let i' : Fin (k+e+1) := ⟨i.val,by omega⟩
  refine ⟨e+2,BoundedLoop.program (k+e) i' A,fun s => ?_⟩
  let S (j : ℕ) := extend e ((f^[j]) s)
  let τ (j : ℕ) := (hA ((f^[j]) s)).choose
  have ht (j : ℕ) : τ j≤T ((f^[j]) s) := (hA ((f^[j]) s)).choose_spec.1
  have hb (j : ℕ) : Eval A (S j) (τ j) (S (j+1)) := by
    have he := (hA ((f^[j]) s)).choose_spec.2
    simpa only [S,Function.iterate_succ_apply'] using he
  have he := BoundedLoop.eval_program (k+e) i' A S τ (fun j _ => hb j)
  have hs : S 0=extend e s := rfl
  have hl : (S 0 i').length=(s i).length := by rw [hs,extend_front]
  rw [hl,hs,state_extend,state_extend] at he
  have hn := total_mono (s i).length τ (fun j => T ((f^[j]) s)) (fun j _ => ht j)
  exact ⟨_,by dsimp only; omega,he⟩

 theorem countedLoop_bound (i : Fin (k+1)) {f : Stores k → Stores k} {T B : Stores k → ℕ}
    (hf : Realizes f T) (hB : ∀s j,j<(s i).length → T ((f^[j]) s)≤B s) :
    Realizes (fun s => (f^[(s i).length]) s) (fun s => (B s+10)*(s i).length+2) := by
  apply monotone (countedLoop i hf)
  intro s
  exact BoundedLoop.program_bound _ _ _ (hB s)

end VariableWL.Computation.Stack.Procedure

namespace VariableWL.Computation.Stack.Procedure
open Code
variable {k : ℕ}

@[simp] theorem extend_front' (e : ℕ) (s : Stores k) (i : Fin (k+1)) :
    extend e s (front k e i)=s i := extend_front e s i

 theorem state_base (s : Stores k) : BoundedLoop.state k s 0=extend 2 s := by
  simpa only [extend_zero,Nat.add_zero] using state_extend 0 s

attribute [local simp] BoundedLoop.counter_ne BoundedLoop.scratch_ne BoundedLoop.counter_scratch

 theorem extend_update (e : ℕ) (s : Stores k) (i : Fin (k+1)) (w : Word) :
    Function.update (extend e s) (front k e i) w=extend e (Function.update s i w) := by
  funext j
  by_cases hj : j.val<k+1
  · have he : j=front k e ⟨j.val,hj⟩ := Fin.ext rfl
    rw [he]
    by_cases hi : (⟨j.val,hj⟩ : Fin (k+1))=i
    · rw [hi,Function.update_self,extend_front',Function.update_self]
    · have hne : front k e ⟨j.val,hj⟩≠front k e i := fun h => hi ((front k e).injective h)
      rw [Function.update_of_ne hne,extend_front',extend_front',Function.update_of_ne hi]
  · have hi : j≠front k e i := by
      intro he
      have hv := congrArg Fin.val he
      change j.val=i.val at hv
      omega
    rw [Function.update_of_ne hi,extend_back _ _ _ (by omega),extend_back _ _ _ (by omega)]

 theorem reverseCopy (j u : Fin (k+1)) (hju : j≠u) (f : Bool → Bool) :
    Realizes (fun s : Stores k => Function.update s u ((s j).reverse.map f++s u))
      (fun s => 6*(s j).length+1) := by
  let j' := front k 1 j
  let u' := front k 1 u
  let tmp : Fin (k+1+1) := ⟨k+1,by omega⟩
  have hjt : j'≠tmp := by
    intro h; have hv := congrArg Fin.val h; change j.val=k+1 at hv; omega
  have hut : u'≠tmp := by
    intro h; have hv := congrArg Fin.val h; change u.val=k+1 at hv; omega
  have hju' : j'≠u' := fun h => hju ((front k 1).injective h)
  refine ⟨1,duplicate j' tmp u' f,fun s => ?_⟩
  have ht : extend 1 s tmp=[] := extend_back _ _ _ (by rfl)
  have he := eval_duplicate j' tmp u' hjt hju' (Ne.symm hut) f (extend 1 s) ht
  simp only [j',u',extend_front',extend_update] at he
  exact ⟨_,le_rfl,he⟩

 theorem transfer (j u : Fin (k+1)) (hju : j≠u) (f : Bool → Bool) :
    Realizes (fun s : Stores k => pairStore s j u [] ((s j).reverse.map f++s u))
      (fun s => 3*(s j).length) :=
  direct (Code.transfer j u f) _ _ (fun s => ⟨_,le_rfl,eval_transfer j u hju f s⟩)

def pushWord (i : Fin (k+1)) : Word → Code k
  | [] => .skip
  | b::w => .seq (pushWord i w) (Code.push i b)

 theorem eval_pushWord (i : Fin (k+1)) (w : Word) (s : Stores k) :
    Eval (pushWord i w) s (2*w.length) (Function.update s i (w++s i)) := by
  induction w with
  | nil => simpa only [pushWord,List.length_nil,List.nil_append,Function.update_eq_self,Nat.mul_zero] using Eval.skip s
  | cons b w ih =>
    have he := Eval.seq ih (eval_push i b (Function.update s i (w++s i)))
    simpa only [pushWord,List.length_cons,Function.update_self,Function.update_idem,
      List.cons_append,show 2*(w.length+1)=2*w.length+1+1 by omega] using he

 theorem prepend (i : Fin (k+1)) (w : Word) :
    Realizes (fun s : Stores k => Function.update s i (w++s i)) (fun _ => 2*w.length) :=
  direct (pushWord i w) _ _ (fun s => ⟨_,le_rfl,eval_pushWord i w s⟩)

 theorem constant (i : Fin (k+1)) (w : Word) :
    Realizes (fun s : Stores k => Function.update s i w) (fun s => 3*(s i).length+1+2*w.length) := by
  have h := seq (clear i) (prepend i w)
  simpa only [Function.comp_def,Function.update_self,Function.update_idem,List.append_nil] using h

 theorem lengthAdd (j u : Fin (k+1)) (hju : j≠u) :
    Realizes (fun s : Stores k => Function.update s u (List.replicate (s j).length true++s u))
      (fun s => 6*(s j).length+1) := by
  simpa only [List.map_const',List.length_reverse] using reverseCopy j u hju (fun _ => true)

 theorem copy (j u : Fin (k+1)) :
    Realizes (fun s : Stores k => Function.update s u (s j))
      (fun s => 9*(s j).length+3*(s u).length+3) := by
  let j' := BoundedLoop.embed k j
  let u' := BoundedLoop.embed k u
  let tmp := BoundedLoop.counter k
  let data := BoundedLoop.scratch k
  let C := Code.seq (duplicate j' tmp data id) (.seq (Code.clear u') (Code.transfer data u' id))
  refine ⟨2,C,fun s => ?_⟩
  let s₀ := BoundedLoop.state k s 0
  let s₁ := Function.update s₀ data (s j).reverse
  let s₂ := Function.update s₁ u' []
  have hd := eval_duplicate j' tmp data (BoundedLoop.counter_ne k j)
    (BoundedLoop.scratch_ne k j) (BoundedLoop.counter_scratch k) id s₀ (by simp [s₀,tmp])
  have hds : Eval (duplicate j' tmp data id) s₀ (6*(s j).length+1) s₁ := by
    simpa only [s₀,j',data,BoundedLoop.state_embed,BoundedLoop.state_scratch,List.map_id_fun,id_eq,List.append_nil] using hd
  have h₁ : s₁ u'=s u := by
    simp [s₁,s₀,u',data]
  have hc := eval_clear u' s₁
  rw [h₁] at hc
  have h₂ : s₂ data=(s j).reverse := by
    simp [s₂,s₁,u',data,Ne.symm (BoundedLoop.scratch_ne k u)]
  have hu₂ : s₂ u'=[] := Function.update_self ..
  have ht := eval_transfer data u' (Ne.symm (BoundedLoop.scratch_ne k u)) id s₂
  rw [h₂,hu₂] at ht
  simp only [List.length_reverse,List.reverse_reverse,List.map_id_fun,id_eq,List.append_nil] at ht
  have hout : pairStore s₂ data u' [] (s j)=BoundedLoop.state k (Function.update s u (s j)) 0 := by
    funext z
    rcases BoundedLoop.cases_index k z with ⟨i,rfl⟩|rfl|rfl
    · by_cases hi : i=u
      · subst i
        simp [pairStore,u']
      · have hne : BoundedLoop.embed k i≠u' := fun h => hi ((BoundedLoop.embed k).injective h)
        simp [pairStore,s₂,s₁,s₀,u',data,hi,show BoundedLoop.embed k i≠BoundedLoop.embed k u from hne]
    · simp [pairStore,s₂,s₁,s₀,u',data,Ne.symm (BoundedLoop.counter_ne k u)]
    · simp [pairStore,u',data,Ne.symm (BoundedLoop.scratch_ne k u)]
  rw [hout] at ht
  have he := Eval.seq hds (Eval.seq hc ht)
  rw [show C=Code.seq (duplicate j' tmp data id) (.seq (Code.clear u') (Code.transfer data u' id)) from rfl]
  refine ⟨(6*(s j).length+1)+1+(3*(s u).length+1+3*(s j).length),by dsimp only; omega,?_⟩
  simpa only [s₀,state_base] using he

end VariableWL.Computation.Stack.Procedure

namespace VariableWL.Computation.Stack.Procedure
open Code
variable {k : ℕ}

def join (k e w : ℕ) : Fin (k+e+w+1) ↪ Fin (k+(e+w)+1) := Fin.castLEEmb (by omega)

 theorem extend_nested (e w : ℕ) (s : Stores k) :
    extend (e+w) s ∘ join k e w=extend w (extend e s) := by
  funext i
  change (if h:i.val<k+1 then s ⟨i.val,h⟩ else []) =
    (if h:i.val<k+e+1 then (if h':i.val<k+1 then s ⟨i.val,h'⟩ else []) else [])
  split_ifs <;> first | rfl | omega

 theorem put_nested (e w : ℕ) (s t : Stores k) :
    put (join k e w) (extend w (extend e t)) (extend (e+w) s)=extend (e+w) t := by
  funext j
  let i : Fin (k+e+w+1) := ⟨j.val,by have := j.isLt; omega⟩
  have he : join k e w i=j := Fin.ext rfl
  rw [←he,put_apply]
  exact (congrFun (extend_nested e w t) i).symm

 theorem localRegisters (e : ℕ) {f : Stores (k+e) → Stores (k+e)} {T : Stores (k+e) → ℕ}
    {g : Stores k → Stores k} {U : Stores k → ℕ}
    (hf : Realizes f T) (hfg : ∀s,f (extend e s)=extend e (g s))
    (hT : ∀s,T (extend e s)≤U s) : Realizes g U := by
  obtain ⟨w,C,hC⟩ := hf
  refine ⟨e+w,rename (join k e w) C,fun s => ?_⟩
  obtain ⟨n,hn,he⟩ := hC (extend e s)
  rw [hfg] at he
  have hr := eval_rename_from (join k e w) (extend (e+w) s)
    (by simpa only [extend_nested] using he)
  rw [put_nested] at hr
  exact ⟨n,hn.trans (hT s),hr⟩

 theorem iterate_update {f : Word → Word} (i : Fin (k+1)) (s : Stores k) (n : ℕ) :
    ((fun t : Stores k=>Function.update t i (f (t i)))^[n]) s=
      Function.update s i ((f^[n]) (s i)) := by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq,Function.update_eq_self]
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,Function.update_self,Function.update_idem,Function.iterate_succ_apply']

 theorem iterate_tail (w : Word) (n : ℕ) : (List.tail^[n]) w=w.drop n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply',ih,List.tail_drop]

 theorem countedPop (bound target : Fin (k+1)) :
    Realizes (fun s : Stores k=>Function.update s target ((s target).drop (s bound).length))
      (fun s=>11*(s bound).length+2) := by
  have h := countedLoop_bound bound (pop target) (B := fun _=>1) (by intros; exact le_rfl)
  simpa only [iterate_update,iterate_tail] using h

end VariableWL.Computation.Stack.Procedure

end OAI
