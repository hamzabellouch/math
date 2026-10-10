import OAI.Computability.WeisfeilerLeman.Programs

namespace OAI

universe uK uA uL

namespace WLTime.TypedStack.Code
variable {K : Type uK} {A : Type uA} [DecidableEq K]

def copy (a b tmp : K) (zero : A) : Code K A :=
  .seq (transfer a tmp zero) (distribute tmp a b zero)

theorem copy_exec (a b tmp : K) (hab : a≠b) (hat : a≠tmp) (hbt : b≠tmp)
    (zero : A) (s : Stacks K A) (ht : s tmp=[]) :
    (copy a b tmp zero).Exec s (12*(s a).length+2) (Function.update s b (s a++s b)) := by
  let mid := Function.update (Function.update s a []) tmp (s a).reverse
  have hf : (transfer a tmp zero).Exec s (5*(s a).length+1) mid := by
    simpa only [ht,List.append_nil] using transfer_exec a tmp hat zero s
  have he := Exec.seq hf (distribute_exec tmp a b hat.symm hbt.symm hab zero mid)
  convert he using 1 <;> try rfl
  · simp [mid,List.length_reverse]
    omega
  · funext k
    by_cases hb : k=b
    · subst k
      simp [mid,hbt,hab.symm]
    · by_cases ha : k=a
      · subst k
        simp [mid,hat,hb]
      · by_cases hk : k=tmp
        · subst k
          simp [mid,hb,ha,ht]
        · simp [mid,hb,ha,hk]

def moveList (a b tmp : K) (zero : A) : Code K A :=
  .seq (transfer a tmp zero) (transfer tmp b zero)

theorem moveList_exec (a b tmp : K) (hab : a≠b) (hat : a≠tmp) (hbt : b≠tmp)
    (zero : A) (s : Stacks K A) (ht : s tmp=[]) :
    (moveList a b tmp zero).Exec s (10*(s a).length+2)
      (Function.update (Function.update s a []) b (s a++s b)) := by
  let mid := Function.update (Function.update s a []) tmp (s a).reverse
  have hf : (transfer a tmp zero).Exec s (5*(s a).length+1) mid := by
    simpa only [ht,List.append_nil] using transfer_exec a tmp hat zero s
  have he := Exec.seq hf (transfer_exec tmp b hbt.symm zero mid)
  convert he using 1 <;> try rfl
  · simp [mid,List.length_reverse]
    omega
  · funext k
    by_cases hb : k=b
    · subst k
      simp [mid,hbt,hab.symm]
    · by_cases ha : k=a
      · subst k
        simp [mid,hat,hb]
      · by_cases hk : k=tmp
        · subst k
          simp [mid,hb,ha,ht]
        · simp [mid,hb,ha,hk]

end WLTime.TypedStack.Code

namespace WLTime.UnaryPrograms
open TypedStack
variable {K : Type uK} [DecidableEq K]

def numeral (n : ℕ) : List Bool := List.replicate n true

def scan : List Bool → ℕ × List Bool
  | [] => (0,[])
  | false::xs => (0,xs)
  | true::xs => let p := scan xs; (p.1+1,p.2)

def isTrue (a : K) (v : Tops K Bool) : Bool := decide (v a=some true)
def readLoop (a b : K) : Code K Bool :=
  .loop (isTrue a) (.seq (.push b true) (.pop a))
def read (a b : K) : Code K Bool := .seq (readLoop a b) (.pop a)

def prefixTail : List Bool → List Bool
  | [] => []
  | false::xs => false::xs
  | true::xs => prefixTail xs

@[simp] theorem prefixTail_tail (xs : List Bool) : (prefixTail xs).tail=(scan xs).2 := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [prefixTail,scan,ih]

theorem readLoop_exec (a b : K) (hab : a≠b) (s : Stacks K Bool) :
    (readLoop a b).Exec s (5*(scan (s a)).1+1)
      (Function.update (Function.update s a (prefixTail (s a))) b
        (numeral (scan (s a)).1++s b)) := by
  generalize hx : s a=xs
  induction xs generalizing s with
  | nil =>
    have he : Function.update (Function.update s a (prefixTail [])) b (numeral (scan []).1++s b)=s := by
      simp only [prefixTail,scan,numeral,List.replicate_zero,List.nil_append]
      rw [← hx,Function.update_eq_self,Function.update_eq_self]
    rw [he]
    exact .loop_false (by simp [isTrue,tops,hx])
  | cons x xs ih =>
    cases x with
    | false =>
      have he : Function.update (Function.update s a (prefixTail (false::xs))) b
          (numeral (scan (false::xs)).1++s b)=s := by
        simp only [prefixTail,scan,numeral,List.replicate_zero,List.nil_append]
        rw [← hx,Function.update_eq_self,Function.update_eq_self]
      rw [he]
      exact .loop_false (by simp [isTrue,tops,hx])
    | true =>
      let mid := Function.update (Function.update s b (true::s b)) a xs
      have hma : mid a=xs := by simp [mid]
      have hf : Code.Exec (.seq (.push b true) (.pop a)) s 4 mid := by
        have hp := Code.Exec.seq (Code.Exec.push s b true) (Code.Exec.pop _ a)
        simpa only [Function.update_of_ne hab,hx,List.tail_cons] using hp
      have hr := ih mid hma
      have he : Function.update (Function.update mid a (prefixTail xs)) b (numeral (scan xs).1++mid b)=
          Function.update (Function.update s a (prefixTail (true::xs))) b
            (numeral (scan (true::xs)).1++s b) := by
        funext k
        by_cases hb : k=b
        · subst k
          simp [mid,hab.symm,scan,numeral,List.replicate_add,List.append_assoc]
        · by_cases ha : k=a
          · subst k; simp [mid,hb,prefixTail]
          · simp [mid,hb,ha]
      rw [he] at hr
      have hh := Code.Exec.loop_true (p:=isTrue a) (by simp [isTrue,tops,hx]) hf hr
      convert hh using 1 <;> try rfl
      simp only [scan]
      omega

theorem read_exec (a b : K) (hab : a≠b) (s : Stacks K Bool) :
    (read a b).Exec s (5*(scan (s a)).1+3)
      (Function.update (Function.update s a (scan (s a)).2) b (numeral (scan (s a)).1++s b)) := by
  have he := Code.Exec.seq (readLoop_exec a b hab s) (Code.Exec.pop _ a)
  convert he using 1 <;> try rfl
  funext k
  by_cases ha : k=a
  · subst k; simp [hab]
  · by_cases hb : k=b
    · subst k; simp [ha]
    · simp [ha,hb]

@[simp] theorem scan_numeral (n : ℕ) (xs : List Bool) : scan (numeral n++false::xs)=(n,xs) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (let p := scan (numeral n++false::xs); (p.1+1,p.2))=(n+1,xs)
    rw [ih]

theorem scan_le (xs : List Bool) : (scan xs).1 ≤ xs.length := by
  induction xs with
  | nil => simp [scan]
  | cons x xs ih =>
    cases x
    · simp [scan]
    · simp only [scan,List.length_cons]; omega

end WLTime.UnaryPrograms

namespace WLTime.TypedStack.Code
variable {K : Type uK} {L : Type uL} {A : Type uA} [DecidableEq K] [DecidableEq L]

def relabel (f : K → L) : Code K A → Code L A
  | .skip => .skip
  | .push k x => .push (f k) x
  | .pushDyn k g => .pushDyn (f k) (fun v => g (v ∘ f))
  | .pop k => .pop (f k)
  | .seq a b => .seq (relabel f a) (relabel f b)
  | .branch p a b => .branch (fun v => p (v ∘ f)) (relabel f a) (relabel f b)
  | .loop p a => .loop (fun v => p (v ∘ f)) (relabel f a)

theorem update_sum_inr (e : L → List A) (s : K → List A) (k : K) (xs : List A) :
    Function.update (Sum.elim e s) (.inr k) xs=Sum.elim e (Function.update s k xs) := by
  funext a
  cases a <;> simp

theorem relabel_inr_exec {c : Code K A} {s t out} (h : c.Exec s t out) (e : L → List A) :
    (c.relabel (Sum.inr : K → L ⊕ K)).Exec (Sum.elim e s) t (Sum.elim e out) := by
  induction h with
  | skip s => exact .skip _
  | push s k x => simpa only [relabel,update_sum_inr,Sum.elim_inr] using Exec.push (Sum.elim e s) (.inr k) x
  | pushDyn s k f =>
    have ht : tops (Sum.elim e s) ∘ Sum.inr=tops s := rfl
    simpa only [relabel,update_sum_inr,Sum.elim_inr,ht] using Exec.pushDyn (Sum.elim e s) (.inr k) (fun v => f (v ∘ Sum.inr))
  | pop s k => simpa only [relabel,update_sum_inr,Sum.elim_inr] using Exec.pop (Sum.elim e s) (.inr k)
  | seq first second ih1 ih2 => exact .seq ih1 ih2
  | branch_true hp body ih => exact .branch_true hp ih
  | branch_false hp body ih => exact .branch_false hp ih
  | loop_false hp => exact .loop_false hp
  | loop_true hp body rest ih1 ih2 => exact .loop_true hp ih1 ih2

end WLTime.TypedStack.Code

namespace WLTime.UnaryPrograms
open TypedStack
variable {K : Type uK} [DecidableEq K]

def repeatN (base : K) (c : Code K Bool) : Code (Fin 2 ⊕ K) Bool :=
  .seq (Code.copy (.inr base) (.inl 0) (.inl 1) false)
    (.loop (Code.nonempty (.inl 0))
      (.seq (c.relabel Sum.inr) (.pop (.inl 0))))

def extra (n : ℕ) : Fin 2 → List Bool := fun i => if i=0 then numeral n else []

theorem extra_succ_update (n : ℕ) (s : Stacks K Bool) :
    Function.update (Sum.elim (extra (n+1)) s) (.inl 0)
      (Sum.elim (extra (n+1)) s (.inl 0)).tail=Sum.elim (extra n) s := by
  funext i
  cases i with
  | inl j => fin_cases j <;> simp [extra,numeral]
  | inr j => simp

theorem countdown_exec (c : Code K Bool) (f : Stacks K Bool → Stacks K Bool)
    (P : Stacks K Bool → Prop) (B : ℕ)
    (hp : ∀ s, P s → P (f s))
    (hc : ∀ s, P s → ∃ t≤B,c.Exec s t (f s))
    (n : ℕ) (s : Stacks K Bool) (hs : P s) :
    ∃ t≤n*(B+3)+1,
      (Code.loop (Code.nonempty (.inl 0))
        (.seq (c.relabel Sum.inr) (.pop (.inl 0))) : Code (Fin 2 ⊕ K) Bool).Exec
        (Sum.elim (extra n) s) t (Sum.elim (extra 0) (f^[n] s)) := by
  induction n generalizing s with
  | zero =>
    refine ⟨1,by omega,?_⟩
    exact .loop_false (by simp [Code.nonempty,tops,extra,numeral])
  | succ n ih =>
    obtain ⟨u,hu,he⟩ := hc s hs
    have he' := Code.relabel_inr_exec he (extra (n+1))
    have hb := Code.Exec.seq he' (Code.Exec.pop _ (.inl 0))
    rw [extra_succ_update] at hb
    obtain ⟨v,hv,hr⟩ := ih (f s) (hp s hs)
    have hh := Code.Exec.loop_true (p:=Code.nonempty (.inl 0))
      (by simp [Code.nonempty,tops,extra,numeral]) hb hr
    refine ⟨u+2+v+1,?_,?_⟩
    · nlinarith
    · simpa only [Function.iterate_succ_apply] using hh

theorem repeat_exec (base : K) (c : Code K Bool) (f : Stacks K Bool → Stacks K Bool)
    (P : Stacks K Bool → Prop) (B n : ℕ)
    (hp : ∀ s,P s → P (f s))
    (hc : ∀ s,P s → ∃ t≤B,c.Exec s t (f s))
    (s : Stacks K Bool) (hs : P s) (hb : s base=numeral n) :
    ∃ t≤n*(B+15)+3,
      (repeatN base c).Exec (Sum.elim (extra 0) s) t
        (Sum.elim (extra 0) (f^[n] s)) := by
  have hf := Code.copy_exec (.inr base : Fin 2 ⊕ K) (.inl 0) (.inl 1)
    (by simp) (by simp) (by simp) false (Sum.elim (extra 0) s) (by simp [extra])
  have he : Function.update (Sum.elim (extra 0) s) (.inl 0)
      (Sum.elim (extra 0) s (.inr base)++Sum.elim (extra 0) s (.inl 0))=
      Sum.elim (extra n) s := by
    funext i
    cases i with
    | inl j => fin_cases j <;> simp [extra,numeral,hb]
    | inr j => simp
  rw [he] at hf
  obtain ⟨u,hu,hr⟩ := countdown_exec c f P B hp hc n s hs
  refine ⟨_,?_,Code.Exec.seq hf hr⟩
  simp only [Sum.elim_inr,hb,numeral,List.length_replicate]
  nlinarith

end WLTime.UnaryPrograms

namespace WLTime.TypedStack.Code
variable {K : Type uK} {L : Type uL} {A : Type uA} [DecidableEq K] [DecidableEq L]

noncomputable def liftStacks (f : K → L) (frame : Stacks L A) (s : Stacks K A) : Stacks L A := by
  classical
  exact fun l => if h : ∃ k,f k=l then s h.choose else frame l

omit [DecidableEq K] [DecidableEq L] in
theorem liftStacks_apply (f : K → L) (hf : Function.Injective f)
    (frame : Stacks L A) (s : Stacks K A) (k : K) : liftStacks f frame s (f k)=s k := by
  classical
  have h : ∃ a,f a=f k := ⟨k,rfl⟩
  rw [liftStacks,dite_eq_left h]
  exact congrArg s (hf h.choose_spec)

theorem liftStacks_update (f : K → L) (hf : Function.Injective f)
    (frame : Stacks L A) (s : Stacks K A) (k : K) (xs : List A) :
    liftStacks f frame (Function.update s k xs)=Function.update (liftStacks f frame s) (f k) xs := by
  classical
  funext l
  by_cases hl : l=f k
  · subst l
    simp only [liftStacks_apply f hf,Function.update_self]
  · rw [Function.update_of_ne hl]
    unfold liftStacks
    split_ifs with h
    · have hne : h.choose≠k := by
        intro hk
        exact hl (h.choose_spec.symm.trans (congrArg f hk))
      exact Function.update_of_ne hne _ _
    · rfl

omit [DecidableEq K] [DecidableEq L] in
theorem liftStacks_tops (f : K → L) (hf : Function.Injective f)
    (frame : Stacks L A) (s : Stacks K A) : tops (liftStacks f frame s) ∘ f=tops s := by
  funext k
  simp only [Function.comp_apply,tops,liftStacks_apply f hf]

theorem relabel_exec (f : K → L) (hf : Function.Injective f)
    {c : Code K A} {s t out} (h : c.Exec s t out) (frame : Stacks L A) :
    (c.relabel f).Exec (liftStacks f frame s) t (liftStacks f frame out) := by
  induction h with
  | skip s => exact .skip _
  | push s k x =>
    simpa only [relabel,liftStacks_update f hf,liftStacks_apply f hf] using
      Exec.push (liftStacks f frame s) (f k) x
  | pushDyn s k g =>
    simpa only [relabel,liftStacks_update f hf,liftStacks_apply f hf,liftStacks_tops f hf] using
      Exec.pushDyn (liftStacks f frame s) (f k) (fun v => g (v ∘ f))
  | pop s k =>
    simpa only [relabel,liftStacks_update f hf,liftStacks_apply f hf] using
      Exec.pop (liftStacks f frame s) (f k)
  | seq first second ih1 ih2 => exact .seq ih1 ih2
  | branch_true hp body ih =>
    exact .branch_true (by simpa only [liftStacks_tops f hf] using hp) ih
  | branch_false hp body ih =>
    exact .branch_false (by simpa only [liftStacks_tops f hf] using hp) ih
  | loop_false hp => exact .loop_false (by simpa only [liftStacks_tops f hf] using hp)
  | loop_true hp body rest ih1 ih2 =>
    exact .loop_true (by simpa only [liftStacks_tops f hf] using hp) ih1 ih2

theorem relabel_exec_of_maps (f : K → L) (hf : Function.Injective f)
    {c : Code K A} {s t out} (h : c.Exec s t out) (s' out' : Stacks L A)
    (hs : ∀ k,s' (f k)=s k) (ho : ∀ k,out' (f k)=out k)
    (hframe : ∀ l,(∀ k,f k≠l) → out' l=s' l) :
    (c.relabel f).Exec s' t out' := by
  classical
  have hi : liftStacks f s' s=s' := by
    funext l
    unfold liftStacks
    split_ifs with hh
    · exact (hs hh.choose).symm.trans (congrArg s' hh.choose_spec)
    · rfl
  have he : liftStacks f s' out=out' := by
    funext l
    unfold liftStacks
    split_ifs with hh
    · exact (ho hh.choose).symm.trans (congrArg out' hh.choose_spec)
    · exact (hframe l (by simpa only [not_exists] using hh)).symm
  simpa only [hi,he] using relabel_exec f hf h s'
end WLTime.TypedStack.Code

namespace WLTime.TypedStack

structure Program (K : Type uK) where
  scratch : ℕ
  code : Code (Fin scratch ⊕ K) Bool

namespace Program
variable {K : Type uK} [DecidableEq K]

def ambient (p : Program K) (s : Stacks K Bool) : Stacks (Fin p.scratch ⊕ K) Bool :=
  Sum.elim (fun _ => []) s

def Exec (p : Program K) (s : Stacks K Bool) (t : ℕ) (out : Stacks K Bool) : Prop :=
  p.code.Exec (p.ambient s) t (p.ambient out)

def embed {a b : ℕ} (j : Fin a → Fin b) : Fin a ⊕ K → Fin b ⊕ K := Sum.map j id

omit [DecidableEq K] in
theorem embed_injective {a b : ℕ} (j : Fin a → Fin b) (hj : Function.Injective j) :
    Function.Injective (embed (K:=K) j) := Sum.map_injective.mpr ⟨hj,Function.injective_id⟩

theorem raise_exec (p : Program K) {s t out} (h : p.Exec s t out)
    {N : ℕ} (j : Fin p.scratch → Fin N) (hj : Function.Injective j) :
    (p.code.relabel (embed (K:=K) j)).Exec
      (Sum.elim (fun _ : Fin N => []) s) t (Sum.elim (fun _ : Fin N => []) out) := by
  apply Code.relabel_exec_of_maps _ (embed_injective j hj) h
  · intro k; cases k <;> rfl
  · intro k; cases k <;> rfl
  · intro l hl
    cases l with
    | inl x => rfl
    | inr x => exact False.elim (hl (.inr x) rfl)

def ofCode (c : Code K Bool) : Program K := ⟨0,c.relabel Sum.inr⟩

theorem ofCode_exec {c : Code K Bool} {s t out} (h : c.Exec s t out) :
    (ofCode c).Exec s t out := Code.relabel_inr_exec h (fun _ => [])

def seq (p q : Program K) : Program K :=
  ⟨p.scratch+q.scratch,.seq
    (p.code.relabel (embed (Fin.castAdd q.scratch)))
    (q.code.relabel (embed (Fin.natAdd p.scratch)))⟩

theorem seq_exec {p q : Program K} {s t u mid out}
    (hp : p.Exec s t mid) (hq : q.Exec mid u out) :
    (seq p q).Exec s (t+u) out := by
  exact .seq (raise_exec p hp _ (Fin.castAdd_injective _ _))
    (raise_exec q hq _ (Fin.natAdd_injective _ _))

def branch (test : Tops K Bool → Bool) (p q : Program K) : Program K :=
  ⟨p.scratch+q.scratch,.branch (fun v => test (v ∘ Sum.inr))
    (p.code.relabel (embed (Fin.castAdd q.scratch)))
    (q.code.relabel (embed (Fin.natAdd p.scratch)))⟩

theorem branch_true {test : Tops K Bool → Bool} {p q : Program K} {s t out}
    (ht : test (tops s)=true) (h : p.Exec s t out) :
    (branch test p q).Exec s (t+1) out := by
  exact .branch_true ht (raise_exec p h _ (Fin.castAdd_injective _ _))

theorem branch_false {test : Tops K Bool → Bool} {p q : Program K} {s t out}
    (ht : test (tops s)=false) (h : q.Exec s t out) :
    (branch test p q).Exec s (t+1) out := by
  exact .branch_false ht (raise_exec q h _ (Fin.natAdd_injective _ _))

def loop (test : Tops K Bool → Bool) (p : Program K) : Program K :=
  ⟨p.scratch,.loop (fun v => test (v ∘ Sum.inr)) p.code⟩

theorem loop_false {test : Tops K Bool → Bool} {p : Program K} {s}
    (h : test (tops s)=false) : (loop test p).Exec s 1 s := .loop_false h

theorem loop_true {test : Tops K Bool → Bool} {p : Program K} {s t u mid out}
    (ht : test (tops s)=true) (hb : p.Exec s t mid)
    (hr : (loop test p).Exec mid u out) : (loop test p).Exec s (t+u+1) out :=
  .loop_true ht hb hr

def skip : Program K := ofCode .skip
def push (a : K) (b : Bool) : Program K := ofCode (.push a b)
def pop (a : K) : Program K := ofCode (.pop a)
def clear (a : K) : Program K := ofCode (Code.clear a)
def read (a b : K) : Program K := ofCode (UnaryPrograms.read a b)
def copy (a b : K) : Program K :=
  ⟨1,Code.copy (.inr a) (.inr b) (.inl 0) false⟩
def moveList (a b : K) : Program K :=
  ⟨1,Code.moveList (.inr a) (.inr b) (.inl 0) false⟩

theorem skip_exec (s : Stacks K Bool) : (skip : Program K).Exec s 1 s := ofCode_exec (.skip s)
theorem push_exec (a : K) (b : Bool) (s : Stacks K Bool) :
    (push a b).Exec s 2 (Function.update s a (b::s a)) := ofCode_exec (.push s a b)
theorem pop_exec (a : K) (s : Stacks K Bool) :
    (pop a).Exec s 2 (Function.update s a (s a).tail) := ofCode_exec (.pop s a)
theorem clear_exec (a : K) (s : Stacks K Bool) :
    (clear a).Exec s (3*(s a).length+1) (Function.update s a []) :=
  ofCode_exec (Code.clear_exec a s)
theorem read_exec (a b : K) (hab : a≠b) (s : Stacks K Bool) :
    (read a b).Exec s (5*(UnaryPrograms.scan (s a)).1+3)
      (Function.update (Function.update s a (UnaryPrograms.scan (s a)).2) b
        (UnaryPrograms.numeral (UnaryPrograms.scan (s a)).1++s b)) :=
  ofCode_exec (UnaryPrograms.read_exec a b hab s)

theorem copy_exec (a b : K) (hab : a≠b) (s : Stacks K Bool) :
    (copy a b).Exec s (12*(s a).length+2) (Function.update s b (s a++s b)) := by
  simp only [Exec,copy,ambient]
  have h := Code.copy_exec (.inr a : Fin 1 ⊕ K) (.inr b) (.inl 0)
    (by simpa using hab) (by simp) (by simp) false (Sum.elim (fun _ : Fin 1 => []) s) rfl
  convert h using 1; simp only [Sum.elim_inr,Code.update_sum_inr]; rfl

theorem moveList_exec (a b : K) (hab : a≠b) (s : Stacks K Bool) :
    (moveList a b).Exec s (10*(s a).length+2)
      (Function.update (Function.update s a []) b (s a++s b)) := by
  simp only [Exec,moveList,ambient]
  have h := Code.moveList_exec (.inr a : Fin 1 ⊕ K) (.inr b) (.inl 0)
    (by simpa using hab) (by simp) (by simp) false (Sum.elim (fun _ : Fin 1 => []) s) rfl
  convert h using 1; simp only [Sum.elim_inr,Code.update_sum_inr]; rfl

def merge (a b : ℕ) : Fin a ⊕ (Fin b ⊕ K) ≃ Fin (a+b) ⊕ K :=
  (Equiv.sumAssoc (Fin a) (Fin b) K).symm.trans
    (Equiv.sumCongr finSumFinEquiv (Equiv.refl K))

omit [DecidableEq K] in
@[simp] theorem merge_left (a b : ℕ) (i : Fin a) :
    merge (K:=K) a b (.inl i)=.inl (i.castAdd b) := rfl
omit [DecidableEq K] in
@[simp] theorem merge_middle (a b : ℕ) (i : Fin b) :
    merge (K:=K) a b (.inr (.inl i))=.inl (i.natAdd a) := rfl
omit [DecidableEq K] in
@[simp] theorem merge_right (a b : ℕ) (i : K) :
    merge (K:=K) a b (.inr (.inr i))=.inr i := rfl

def allocate {n : ℕ} (p : Program (Fin n ⊕ K)) : Program K :=
  ⟨p.scratch+n,p.code.relabel (merge p.scratch n)⟩

theorem local_exec {n : ℕ} {p : Program (Fin n ⊕ K)} {s t out}
    (h : p.Exec (Sum.elim (fun _ => []) s) t (Sum.elim (fun _ => []) out)) :
    (allocate p).Exec s t out := by
  apply Code.relabel_exec_of_maps _ (Equiv.injective _) h
  · intro k; cases k with
    | inl i => rfl
    | inr i => cases i <;> rfl
  · intro k; cases k with
    | inl i => rfl
    | inr i => cases i <;> rfl
  · intro l hl
    exact False.elim (hl ((merge p.scratch n).symm l) (Equiv.apply_symm_apply _ l))

def repeatN (base : K) (p : Program K) : Program K :=
  ⟨2+p.scratch,(UnaryPrograms.repeatN (.inr base) p.code).relabel (merge 2 p.scratch)⟩

theorem repeat_exec (base : K) (p : Program K) (f : Stacks K Bool → Stacks K Bool)
    (P : Stacks K Bool → Prop) (B n : ℕ)
    (hp : ∀ s,P s → P (f s))
    (hc : ∀ s,P s → ∃ t≤B,p.Exec s t (f s))
    (s : Stacks K Bool) (hs : P s) (hb : s base=UnaryPrograms.numeral n) :
    ∃ t≤n*(B+15)+3,(repeatN base p).Exec s t (f^[n] s) := by
  let g : Stacks (Fin p.scratch ⊕ K) Bool → Stacks (Fin p.scratch ⊕ K) Bool :=
    fun z => p.ambient (f (z ∘ Sum.inr))
  let Q : Stacks (Fin p.scratch ⊕ K) Bool → Prop :=
    fun z => ∃ s,z=p.ambient s ∧ P s
  have hg (s) : g (p.ambient s)=p.ambient (f s) := rfl
  have hi (n) (s) : g^[n] (p.ambient s)=p.ambient (f^[n] s) := by
    induction n generalizing s with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply,hg,ih,Function.iterate_succ_apply]
  have hp' : ∀ z,Q z → Q (g z) := by
    rintro _ ⟨s,rfl,hs⟩
    exact ⟨f s,hg s,hp s hs⟩
  have hc' : ∀ z,Q z → ∃ t≤B,p.code.Exec z t (g z) := by
    rintro _ ⟨s,rfl,hs⟩
    exact hc s hs
  obtain ⟨t,ht,he⟩ := UnaryPrograms.repeat_exec (.inr base : Fin p.scratch ⊕ K) p.code g Q B n hp' hc'
    (p.ambient s) ⟨s,rfl,hs⟩ (show p.ambient s (.inr base)=UnaryPrograms.numeral n from hb)
  rw [hi] at he
  refine ⟨t,ht,?_⟩
  apply Code.relabel_exec_of_maps _ (Equiv.injective _) he
  · intro k; cases k with
    | inl i => fin_cases i <;> rfl
    | inr i => cases i <;> rfl
  · intro k; cases k with
    | inl i => fin_cases i <;> rfl
    | inr i => cases i <;> rfl
  · intro l hl
    exact False.elim (hl ((merge 2 p.scratch).symm l) (Equiv.apply_symm_apply _ l))

end Program
end WLTime.TypedStack

end OAI
