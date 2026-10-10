import OAI.Computability.WeisfeilerLeman.Arithmetic

namespace OAI

universe uK uL

namespace WLTime.UnaryPrograms
open TypedStack
variable {K : Type uK} [DecidableEq K]

def skipFieldLoop (a : K) : Code K Bool := .loop (isTrue a) (.pop a)
def skipField (a : K) : Program K := Program.ofCode (.seq (skipFieldLoop a) (.pop a))

theorem skipFieldLoop_exec (a : K) (s : Stacks K Bool) :
    (skipFieldLoop a).Exec s (3*(scan (s a)).1+1)
      (Function.update s a (prefixTail (s a))) := by
  generalize hx : s a=xs
  induction xs generalizing s with
  | nil =>
    have he : Function.update s a (prefixTail [])=s := by
      simpa only [prefixTail,←hx] using Function.update_eq_self a s
    rw [he]
    exact .loop_false (by simp [isTrue,tops,hx])
  | cons x xs ih =>
    cases x with
    | false =>
      have he : Function.update s a (prefixTail (false::xs))=s := by
        simpa only [prefixTail,←hx] using Function.update_eq_self a s
      rw [he]
      exact .loop_false (by simp [isTrue,tops,hx])
    | true =>
      have hr := ih (Function.update s a xs) (by simp)
      simp only [Function.update_idem] at hr
      have hp : Code.Exec (.pop a) s 2 (Function.update s a xs) := by
        simpa only [hx,List.tail_cons] using Code.Exec.pop s a
      have he := Code.Exec.loop_true (p:=isTrue a) (by simp [isTrue,tops,hx]) hp hr
      convert he using 1 <;> try rfl
      simp only [scan]
      omega

theorem skipField_exec (a : K) (s : Stacks K Bool) :
    (skipField a).Exec s (3*(scan (s a)).1+3) (Function.update s a (scan (s a)).2) := by
  apply Program.ofCode_exec
  have he := Code.Exec.seq (skipFieldLoop_exec a s) (Code.Exec.pop _ a)
  simpa only [Function.update_self,prefixTail_tail,Function.update_idem,Nat.add_assoc] using he

theorem scan_tail_le (xs : List Bool) : (scan xs).2.length≤xs.length := by
  induction xs with
  | nil => simp [scan]
  | cons b xs ih => cases b <;> simp only [scan,List.length_cons] <;> omega

def tailField (xs : List Bool) := (scan xs).2

def skipEntry (a : K) : Program K :=
  Program.seq (skipField a) (Program.seq (skipField a) (skipField a))

theorem skipEntry_exec (a : K) (s : Stacks K Bool) :
    ∃ t≤9*(s a).length+9,(skipEntry a).Exec s t (Function.update s a (tailField^[3] (s a))) := by
  have h1 := skipField_exec a s
  have h2 := skipField_exec a (Function.update s a (tailField (s a)))
  have h3 := skipField_exec a (Function.update s a (tailField (tailField (s a))))
  simp only [Function.update_self,Function.update_idem] at h2 h3
  have he := Program.seq_exec h1 (Program.seq_exec h2 h3)
  refine ⟨_,?_,he⟩
  have ha := scan_le (s a)
  have hb := scan_le (tailField (s a))
  have hc := scan_le (tailField (tailField (s a)))
  have hd := scan_tail_le (s a)
  have hf := scan_tail_le (tailField (s a))
  dsimp only [tailField] at *
  omega

def seek (a index : K) : Program K := Program.repeatN index (skipEntry a)

theorem tailField_iterate_le (n : ℕ) (xs : List Bool) :
    (tailField^[n] xs).length≤xs.length := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact (ih _).trans (scan_tail_le xs)

theorem seek_exec (a index : K) (n : ℕ) (s : Stacks K Bool)
    (hi : s index=numeral n) :
    ∃ t≤n*(9*(s a).length+24)+3,
      (seek a index).Exec s t (Function.update s a (tailField^[3*n] (s a))) := by
  let f := fun s : Stacks K Bool => Function.update s a (tailField^[3] (s a))
  let P := fun z : Stacks K Bool => (z a).length≤(s a).length
  have hp : ∀z,P z → P (f z) := by
    intro z hz
    simpa only [P,f,Function.update_self] using (tailField_iterate_le 3 (z a)).trans hz
  have hc : ∀z,P z → ∃t≤9*(s a).length+9,(skipEntry a).Exec z t (f z) := by
    intro z hz
    obtain ⟨t,ht,he⟩ := skipEntry_exec a z
    exact ⟨t,by dsimp only [P] at hz; omega,he⟩
  have he (n) : f^[n] s=Function.update s a (tailField^[3*n] (s a)) := by
    induction n with
    | zero => simpa only [Function.iterate_zero,Function.id_def,Nat.mul_zero] using
        (Function.update_eq_self a s).symm
    | succ n ih =>
      rw [Function.iterate_succ_apply',ih]
      simp only [f,Function.update_self,Function.update_idem]
      congr 1
      rw [Nat.mul_succ,Nat.add_comm,Function.iterate_add_apply]
  obtain ⟨t,ht,hh⟩ := Program.repeat_exec index (skipEntry a) f P (9*(s a).length+9) n hp hc s le_rfl hi
  rw [he] at hh
  exact ⟨t,by omega,hh⟩

def prependRecord (a b : K) : Program K := Program.seq (Program.push b false) (Program.copy a b)

theorem prependRecord_exec (a b : K) (hab : a≠b) (n : ℕ) (s : Stacks K Bool)
    (ha : s a=numeral n) :
    (prependRecord a b).Exec s (12*n+4) (Function.update s b (numeral n++false::s b)) := by
  have he := Program.seq_exec (Program.push_exec b false s)
    (Program.copy_exec a b hab (Function.update s b (false::s b)))
  simpa only [prependRecord,Function.update_of_ne hab,Function.update_self,Function.update_idem,ha,
    numeral,List.length_replicate,Nat.add_comm 2,Nat.add_assoc,Nat.reduceAdd] using he

@[simp] theorem numeral_length (n : ℕ) : (numeral n).length=n := List.length_replicate

theorem numeral_add (n m : ℕ) : numeral (n+m)=numeral n++numeral m :=
  List.replicate_add n m true

def mulAdd (a b c : K) : Program K := Program.repeatN a (Program.copy b c)

theorem mulAdd_exec (a b c : K) (hbc : b≠c)
    (s : Stacks K Bool) (na nb : ℕ) (ha : s a=numeral na) (hb : s b=numeral nb) :
    ∃t≤na*(12*nb+17)+3,
      (mulAdd a b c).Exec s t (Function.update s c (numeral (na*nb)++s c)) := by
  let f := fun z : Stacks K Bool => Function.update z c (z b++z c)
  let P := fun z : Stacks K Bool => z b=numeral nb
  have hp : ∀z,P z → P (f z) := by
    intro z hz
    simpa only [P,f,Function.update_of_ne hbc] using hz
  have hc : ∀z,P z → ∃t≤12*nb+2,(Program.copy b c).Exec z t (f z) := by
    intro z hz
    change z b=numeral nb at hz
    refine ⟨12*nb+2,le_rfl,?_⟩
    simpa only [f,hz,numeral_length] using Program.copy_exec b c hbc z
  have hi (n) : f^[n] s=Function.update s c (numeral (n*nb)++s c) := by
    induction n with
    | zero => simpa only [Function.iterate_zero,Function.id_def,Nat.zero_mul,numeral,
        List.replicate_zero,List.nil_append] using (Function.update_eq_self c s).symm
    | succ n ih =>
      rw [Function.iterate_succ_apply',ih]
      simp only [f,Function.update_of_ne hbc,Function.update_self,Function.update_idem,hb]
      congr 1
      rw [Nat.succ_mul,Nat.add_comm,numeral_add,List.append_assoc]
  obtain ⟨t,ht,he⟩ := Program.repeat_exec a (Program.copy b c) f P (12*nb+2) na hp hc s hb ha
  rw [hi] at he
  exact ⟨t,by omega,he⟩

end WLTime.UnaryPrograms

namespace WLTime.TypedStack.Program
variable {K : Type uK} {L : Type uL} [DecidableEq K] [DecidableEq L]

def relabel (p : Program K) (j : K → L) : Program L :=
  ⟨p.scratch,p.code.relabel (Sum.map id j)⟩

theorem relabel_exec (p : Program K) {j : K → L} (hj : Function.Injective j)
    {s t out} (h : p.Exec s t out) {s' out' : Stacks L Bool}
    (hin : ∀ k,s' (j k)=s k) (hout : ∀ k,out' (j k)=out k)
    (hoff : ∀ l,(∀ k,j k≠l) → s' l=out' l) :
    (p.relabel j).Exec s' t out' := by
  apply Code.relabel_exec_of_maps _ (Sum.map_injective.mpr ⟨Function.injective_id,hj⟩) h
  · intro k; cases k with
    | inl k => rfl
    | inr k => exact hin k
  · intro k; cases k with
    | inl k => rfl
    | inr k => exact hout k
  · intro k hk; cases k with
    | inl k => rfl
    | inr k => exact (hoff k (fun l hl => hk (.inr l) (congrArg Sum.inr hl))).symm

def pushes (a : K) : List Bool → Program K
  | [] => skip
  | b::bs => seq (pushes a bs) (push a b)

theorem pushes_exec (a : K) (bs : List Bool) (s : Stacks K Bool) :
    (pushes a bs).Exec s (2*bs.length+1) (Function.update s a (bs++s a)) := by
  induction bs with
  | nil => simpa only [pushes,List.length_nil,List.nil_append,Nat.mul_zero,Nat.zero_add,Function.update_eq_self]
      using skip_exec s
  | cons b bs ih =>
    have he := seq_exec ih (push_exec a b (Function.update s a (bs++s a)))
    simpa only [pushes,Function.update_self,Function.update_idem,List.cons_append,List.length_cons,
      Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm 2] using he

def overwrite (a b : K) : Program K := seq (clear b) (copy a b)

theorem overwrite_exec (a b : K) (hab : a≠b) (s : Stacks K Bool) :
    (overwrite a b).Exec s (3*(s b).length+12*(s a).length+3) (Function.update s b (s a)) := by
  have h := seq_exec (clear_exec b s) (copy_exec a b hab (Function.update s b []))
  simpa only [overwrite,Function.update_of_ne hab,Function.update_self,Function.update_idem,
    List.append_nil,show 3*(s b).length+1+(12*(s a).length+2)=3*(s b).length+12*(s a).length+3 by omega] using h

def putNat (a : K) (n : ℕ) : Program K := seq (clear a) (pushes a (UnaryPrograms.numeral n))

theorem putNat_exec (a : K) (n : ℕ) (s : Stacks K Bool) :
    (putNat a n).Exec s (3*(s a).length+2*n+2)
      (Function.update s a (UnaryPrograms.numeral n)) := by
  have h := seq_exec (clear_exec a s) (pushes_exec a (UnaryPrograms.numeral n) (Function.update s a []))
  simpa only [putNat,Function.update_self,Function.update_idem,List.append_nil,
    UnaryPrograms.numeral_length,show 3*(s a).length+1+(2*n+1)=3*(s a).length+2*n+2 by omega] using h

def dropN (index dest : K) : Program K := repeatN index (pop dest)

theorem dropN_exec (index dest : K) (n : ℕ) (s : Stacks K Bool)
    (hi : s index=UnaryPrograms.numeral n) :
    ∃ t≤17*n+3,(dropN index dest).Exec s t (Function.update s dest ((s dest).drop n)) := by
  let f := fun s : Stacks K Bool => Function.update s dest (s dest).tail
  have hc (s : Stacks K Bool) (_ : True) : ∃t≤2,(pop dest).Exec s t (f s) := ⟨2,le_rfl,pop_exec dest s⟩
  obtain ⟨t,ht,he⟩ := repeat_exec index (pop dest) f (fun _ => True) 2 n
    (fun _ _ => trivial) hc s trivial hi
  have hf (n) : f^[n] s=Function.update s dest ((s dest).drop n) := by
    induction n with
    | zero => simpa only [Function.iterate_zero,Function.id_def,List.drop_zero] using
        (Function.update_eq_self dest s).symm
    | succ n ih =>
      rw [Function.iterate_succ_apply',ih]
      simp only [f,Function.update_self,Function.update_idem,List.tail_drop]
  rw [hf] at he
  exact ⟨t,by omega,he⟩

def putBit (a b : K) : Program K := seq (clear b)
  (branch (fun v => v a==some true) (push b true) skip)

theorem putBit_exec (a b : K) (hab : a≠b) (s : Stacks K Bool) :
    ∃t≤3*(s b).length+4,(putBit a b).Exec s t
      (Function.update s b (UnaryPrograms.numeral (if (s a).headD false then 1 else 0))) := by
  have hd : (tops (Function.update s b [])) a=(s a).head? := by simp [tops,hab]
  by_cases h : (s a).headD false=true
  · have ht : (s a).head?=some true := by cases ha : s a with
        | nil => simp [ha] at h
        | cons x xs => simp_all
    have he := seq_exec (clear_exec b s)
      (branch_true (test:=fun v => v a==some true) (p:=push b true) (q:=skip) (by simp [hd,ht])
        (push_exec b true (Function.update s b [])))
    refine ⟨_,?_,by
      simpa only [putBit,h,ite_true,UnaryPrograms.numeral,List.replicate_succ,List.replicate_zero,
        Function.update_self,Function.update_idem] using he⟩
    omega
  · have ht : (s a).head?≠some true := by intro hh; cases ha : s a <;> simp_all
    have he := seq_exec (clear_exec b s)
      (branch_false (test:=fun v => v a==some true) (p:=push b true) (q:=skip) (by simp [hd,ht])
        (skip_exec (Function.update s b [])))
    refine ⟨_,?_,by
      simpa only [putBit,show (s a).headD false=false from Bool.eq_false_iff.mpr h,
        Bool.false_eq_true,ite_false,UnaryPrograms.numeral,List.replicate_zero] using he⟩
    omega

end WLTime.TypedStack.Program

namespace WLTime.NatCode
open TypedStack UnaryPrograms

inductive Binary where
  | add | mul | sub
  deriving DecidableEq

def Binary.eval : Binary → ℕ → ℕ → ℕ
  | .add => (·+·)
  | .mul => (·*·)
  | .sub => (·-·)

variable {L : Type uL} [DecidableEq L]

def core (op : Binary) (a b c : L) : Program L := Program.seq (Program.clear c)
  (match op with
  | .add => Program.seq (Program.copy a c) (Program.copy b c)
  | .mul => mulAdd a b c
  | .sub => Program.seq (Program.copy a c) (Program.dropN b c))

theorem core_exec (op : Binary) (a b c : L) (hac : a≠c) (hbc : b≠c)
    (s : Stacks L Bool) (x y B : ℕ) (ha : s a=numeral x) (hb : s b=numeral y)
    (hx : x≤B) (hy : y≤B) (hs : (s c).length≤B) :
    ∃t≤50*(B+1)^2,(core op a b c).Exec s t (Function.update s c (numeral (op.eval x y))) := by
  have ha' : (Function.update s c []) a=numeral x := by simpa only [Function.update_of_ne hac] using ha
  have hb' : (Function.update s c []) b=numeral y := by simpa only [Function.update_of_ne hbc] using hb
  cases op with
  | add =>
    have h1 := Program.copy_exec a c hac (Function.update s c [])
    simp only [ha',Function.update_self,List.append_nil,Function.update_idem] at h1
    have h2 := Program.copy_exec b c hbc (Function.update s c (numeral x))
    simp only [Function.update_of_ne hbc,Function.update_self,hb,Function.update_idem,
      numeral_length] at h2
    have he := Program.seq_exec (Program.clear_exec c s) (Program.seq_exec h1 h2)
    refine ⟨_,?_,by
      simpa only [core,Binary.eval,numeral_length,numeral_add,Nat.add_comm x] using he⟩
    nlinarith [Nat.zero_le (B*B)]
  | mul =>
    obtain ⟨t,ht,he⟩ := mulAdd_exec a b c hbc (Function.update s c []) x y ha' hb'
    have hh := Program.seq_exec (Program.clear_exec c s) he
    refine ⟨_,?_,by simpa only [core,Binary.eval,Function.update_self,List.append_nil,Function.update_idem] using hh⟩
    have hm : x*y≤B*B := Nat.mul_le_mul hx hy
    nlinarith [Nat.zero_le (B*B)]
  | sub =>
    have h1 := Program.copy_exec a c hac (Function.update s c [])
    simp only [ha',Function.update_self,List.append_nil,Function.update_idem,numeral_length] at h1
    obtain ⟨t,ht,h2⟩ := Program.dropN_exec b c y (Function.update s c (numeral x))
      (by simpa only [Function.update_of_ne hbc] using hb)
    simp only [Function.update_self,Function.update_idem,numeral,List.drop_replicate] at h2
    have he := Program.seq_exec (Program.clear_exec c s) (Program.seq_exec h1 h2)
    refine ⟨_,?_,he⟩
    nlinarith [Nat.zero_le (B*B)]

def binary (op : Binary) (a b c : L) : Program L :=
  Program.seq (core op a b c) (Program.seq (Program.clear a) (Program.clear b))

theorem binary_exec (op : Binary) (a b c : L) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (s : Stacks L Bool) (x y B : ℕ) (ha : s a=numeral x) (hb : s b=numeral y)
    (hx : x≤B) (hy : y≤B) (hs : (s c).length≤B) :
    ∃t≤100*(B+1)^2,(binary op a b c).Exec s t
      (Function.update (Function.update (Function.update s c (numeral (op.eval x y))) a []) b []) := by
  obtain ⟨t,ht,he⟩ := core_exec op a b c hac hbc s x y B ha hb hx hy hs
  have hh := Program.seq_exec he (Program.seq_exec
    (Program.clear_exec a (Function.update s c (numeral (op.eval x y))))
    (Program.clear_exec b (Function.update (Function.update s c (numeral (op.eval x y))) a [])))
  simp only [Function.update_of_ne hac,Function.update_of_ne hab.symm,Function.update_of_ne hbc,
    ha,hb,numeral_length] at hh
  refine ⟨_,?_,hh⟩
  nlinarith [Nat.zero_le (B*B)]

def bitAt (word index dest : L) : Program L := Program.allocate
  (Program.seq (Program.copy (.inr word) (.inl (0 : Fin 1)))
    (Program.seq (Program.dropN (.inr index) (.inl 0))
      (Program.seq (Program.putBit (.inl 0) (.inr dest)) (Program.clear (.inl 0)))))

theorem bitAt_exec (word index dest : L)
    (s : Stacks L Bool) (w : List Bool) (n B : ℕ) (hw : s word=w) (hi : s index=numeral n)
    (hn : n≤B) (hwl : w.length≤B) (hd : (s dest).length≤B) :
    ∃t≤100*(B+1)^2,(bitAt word index dest).Exec s t
      (Function.update s dest (numeral (if w.getD n false then 1 else 0))) := by
  let z : Stacks (Fin 1 ⊕ L) Bool := Sum.elim (fun _ => []) s
  let a : Fin 1 ⊕ L := .inl 0
  have h1 := Program.copy_exec (.inr word) a (by simp [a]) z
  have hout : Function.update z a (z (.inr word)++z a)=Function.update z a w := by simp only [z,a,Sum.elim_inr,Sum.elim_inl,hw,List.append_nil]
  rw [hout] at h1
  obtain ⟨t,ht,h2⟩ := Program.dropN_exec (.inr index) a n (Function.update z a w)
    (by simpa only [z,a,Function.update_of_ne (Sum.inr_ne_inl),Sum.elim_inr] using hi)
  simp only [Function.update_self,Function.update_idem] at h2
  obtain ⟨u,hu,h3⟩ := Program.putBit_exec a (.inr dest) (by simp [a]) (Function.update z a (w.drop n))
  simp only [Function.update_self,Function.update_of_ne (show (.inr dest : Fin 1 ⊕ L)≠a by simp [a])] at h3 hu
  have hD : ∀ (w : List Bool) (n : ℕ), (w.drop n).headD false=w.getD n false := by
    intro w n
    induction n generalizing w with
    | zero => cases w <;> rfl
    | succ n ih => cases w with
      | nil => rfl
      | cons a w => exact ih w
  rw [hD] at h3
  have h4 := Program.clear_exec a
    (Function.update (Function.update z a (w.drop n)) (.inr dest)
      (numeral (if w.getD n false then 1 else 0)))
  have he := Program.seq_exec h1 (Program.seq_exec h2 (Program.seq_exec h3 h4))
  have ho : Function.update (Function.update (Function.update z a (w.drop n)) (.inr dest)
      (numeral (if w.getD n false then 1 else 0))) a [] =
      Sum.elim (fun _ : Fin 1 => []) (Function.update s dest (numeral (if w.getD n false then 1 else 0))) := by
    funext j; cases j with
    | inl j =>
      have hj : j=0 := Subsingleton.elim _ _
      subst j
      exact Function.update_self _ _ _
    | inr j => simp only [a,z,Function.update_of_ne (Sum.inr_ne_inl),
        Function.update_apply,Sum.inr.injEq,Sum.elim_inr]
  rw [ho] at he
  refine ⟨_,?_,Program.local_exec he⟩
  have hdrop : (w.drop n).length≤w.length := by rw [List.length_drop]; omega
  simp only [Function.update_of_ne (show a≠(.inr dest : Fin 1 ⊕ L) by simp [a]),
    Function.update_self,z,Sum.elim_inr,hw] at hu ⊢
  nlinarith [Nat.zero_le (B*B)]

end WLTime.NatCode

namespace WLTime.NatCode
open TypedStack UnaryPrograms

inductive Expr (K : Type uK) where
  | const (n : ℕ)
  | var (k : K)
  | binary (op : Binary) (left right : Expr K)
  | bit (index : Expr K)

namespace Expr
variable {K : Type uK} {L : Type uL}

def eval (σ : K → ℕ) (w : List Bool) : Expr K → ℕ
  | .const n => n
  | .var k => σ k
  | .binary op e f => op.eval (e.eval σ w) (f.eval σ w)
  | .bit e => if w.getD (e.eval σ w) false then 1 else 0

def Bounded (σ : K → ℕ) (w : List Bool) (B : ℕ) : Expr K → Prop
  | .const n => n≤B
  | .var k => σ k≤B
  | .binary op e f => e.Bounded σ w B ∧ f.Bounded σ w B ∧ op.eval (e.eval σ w) (f.eval σ w)≤B
  | .bit e => e.Bounded σ w B ∧ 1≤B

theorem eval_le (σ : K → ℕ) (w : List Bool) (B : ℕ) (e : Expr K) (h : e.Bounded σ w B) :
    e.eval σ w≤B := by
  cases e with
  | const => exact h
  | var => exact h
  | binary => exact h.2.2
  | bit e => dsimp only [eval]; split_ifs <;> exact le_trans (by omega) h.2

def charge : Expr K → ℕ
  | .const _ | .var _ => 20
  | .binary _ e f => e.charge+f.charge+100
  | .bit e => e.charge+120

def compile (e : Expr K) : {L : Type uL} → [DecidableEq L] → (K → L) → L → L → Program L :=
  match e with
  | .const n => fun _ρ _word dest => Program.putNat dest n
  | .var k => fun ρ _word dest => Program.overwrite (ρ k) dest
  | .binary op e f => fun ρ word dest => Program.allocate
      (Program.seq (e.compile (Sum.inr ∘ ρ) (.inr word) (.inl (0 : Fin 2)))
        (Program.seq (f.compile (Sum.inr ∘ ρ) (.inr word) (.inl 1))
          (NatCode.binary op (.inl 0) (.inl 1) (.inr dest))))
  | .bit e => fun ρ word dest => Program.allocate
      (Program.seq (e.compile (Sum.inr ∘ ρ) (.inr word) (.inl (0 : Fin 1)))
        (Program.seq (bitAt (.inr word) (.inl 0) (.inr dest)) (Program.clear (.inl 0))))

theorem compile_exec (e : Expr K) [DecidableEq L] (ρ : K → L) (word dest : L)
    (hdw : dest≠word) (hdr : ∀ k,dest≠ρ k) (σ : K → ℕ) (w : List Bool) (B : ℕ)
    (he : e.Bounded σ w B) (hwB : w.length≤B) (s : Stacks L Bool)
    (hs : ∀ k,s (ρ k)=numeral (σ k)) (hw : s word=w) (hd : (s dest).length≤B) :
    ∃t≤e.charge*(B+1)^2,(e.compile ρ word dest).Exec s t
      (Function.update s dest (numeral (e.eval σ w))) := by
  induction e generalizing L with
  | const n =>
    refine ⟨_,?_,by simpa only [compile,eval] using Program.putNat_exec dest n s⟩
    change n≤B at he
    change 3*(s dest).length+2*n+2≤20*(B+1)^2
    nlinarith [Nat.zero_le (B*B)]
  | var k =>
    have hh := Program.overwrite_exec (ρ k) dest (hdr k).symm s
    rw [hs k,numeral_length] at hh
    refine ⟨_,?_,by simpa only [compile,eval] using hh⟩
    change σ k≤B at he
    change 3*(s dest).length+12*σ k+3≤20*(B+1)^2
    nlinarith [Nat.zero_le (B*B)]
  | binary op e f ihe ihf =>
    let z : Stacks (Fin 2 ⊕ L) Bool := Sum.elim (fun _ => []) s
    let a : Fin 2 ⊕ L := .inl 0
    let b : Fin 2 ⊕ L := .inl 1
    obtain ⟨t,ht,h1⟩ := ihe (Sum.inr ∘ ρ) (.inr word) a (by simp [a])
      (fun _ => by simp [a]) he.1 z (fun k => hs k) hw (by simp [z,a])
    obtain ⟨u,hu,h2⟩ := ihf (Sum.inr ∘ ρ) (.inr word) b (by simp [b])
      (fun _ => by simp [b]) he.2.1
      (Function.update z a (numeral (e.eval σ w)))
      (fun k => by simpa only [a,Function.comp_apply,Function.update_of_ne Sum.inr_ne_inl,z,Sum.elim_inr] using hs k)
      (by simpa only [a,Function.update_of_ne Sum.inr_ne_inl,z,Sum.elim_inr] using hw)
      (by simp only [a,b,Function.update_of_ne (by simp : (Sum.inl (1 : Fin 2) : Fin 2 ⊕ L)≠.inl 0),z,Sum.elim_inl,List.length_nil]; omega)
    let zz := Function.update (Function.update z a (numeral (e.eval σ w))) b (numeral (f.eval σ w))
    obtain ⟨v,hv,h3⟩ := binary_exec op a b (.inr dest) (by simp [a,b]) (by simp [a]) (by simp [b])
      zz (e.eval σ w) (f.eval σ w) B
      (by simp [zz,a,b]) (by simp [zz]) (e.eval_le σ w B he.1) (f.eval_le σ w B he.2.1)
      (by simpa only [zz,a,b,Function.update_of_ne Sum.inr_ne_inl,z,Sum.elim_inr] using hd)
    have hh := Program.seq_exec h1 (Program.seq_exec h2 h3)
    have ho : Function.update (Function.update (Function.update zz (.inr dest)
        (numeral (op.eval (e.eval σ w) (f.eval σ w)))) a []) b [] =
        Sum.elim (fun _ : Fin 2 => []) (Function.update s dest
          (numeral (op.eval (e.eval σ w) (f.eval σ w)))) := by
      funext j; cases j with
      | inl j => fin_cases j <;> simp [a,b,zz]
      | inr j => simp only [a,b,zz,Function.update_of_ne Sum.inr_ne_inl,
          Function.update_apply,Sum.inr.injEq,z,Sum.elim_inr]
    rw [ho] at hh
    refine ⟨t+(u+v),?_,Program.local_exec hh⟩
    change t+(u+v)≤(e.charge+f.charge+100)*(B+1)^2
    calc
      _ ≤ e.charge*(B+1)^2+(f.charge*(B+1)^2+100*(B+1)^2) := Nat.add_le_add ht (Nat.add_le_add hu hv)
      _ = _ := by ring
  | bit e ih =>
    let z : Stacks (Fin 1 ⊕ L) Bool := Sum.elim (fun _ => []) s
    let a : Fin 1 ⊕ L := .inl 0
    obtain ⟨t,ht,h1⟩ := ih (Sum.inr ∘ ρ) (.inr word) a (by simp [a])
      (fun _ => by simp [a]) he.1 z (fun k => hs k) hw (by simp [z,a])
    obtain ⟨u,hu,h2⟩ := bitAt_exec (.inr word) a (.inr dest)
      (Function.update z a (numeral (e.eval σ w))) w (e.eval σ w) B
      (by simpa only [a,Function.update_of_ne Sum.inr_ne_inl,z,Sum.elim_inr] using hw)
      (Function.update_self _ _ _) (e.eval_le σ w B he.1) hwB
      (by simpa only [a,Function.update_of_ne Sum.inr_ne_inl,z,Sum.elim_inr] using hd)
    have h3 := Program.clear_exec a
      (Function.update (Function.update z a (numeral (e.eval σ w))) (.inr dest)
        (numeral (if w.getD (e.eval σ w) false then 1 else 0)))
    have hh := Program.seq_exec h1 (Program.seq_exec h2 h3)
    have ho : Function.update (Function.update (Function.update z a (numeral (e.eval σ w))) (.inr dest)
        (numeral (if w.getD (e.eval σ w) false then 1 else 0))) a [] =
        Sum.elim (fun _ : Fin 1 => []) (Function.update s dest (numeral (e.bit.eval σ w))) := by
      funext j; cases j with
      | inl j =>
        have hj : j=0 := Subsingleton.elim _ _
        subst j
        exact Function.update_self _ _ _
      | inr j => simp only [a,z,eval,Function.update_of_ne Sum.inr_ne_inl,
          Function.update_apply,Sum.inr.injEq,Sum.elim_inr]
    rw [ho] at hh
    refine ⟨_,?_,Program.local_exec hh⟩
    simp only [a,Function.update_of_ne Sum.inl_ne_inr,Function.update_self,numeral_length]
    change t+(u+(3*e.eval σ w+1))≤(e.charge+120)*(B+1)^2
    have hv := e.eval_le σ w B he.1
    have hlin : 3*e.eval σ w+1≤20*(B+1)^2 := by nlinarith [Nat.zero_le (B*B)]
    calc
      _ ≤ e.charge*(B+1)^2+(100*(B+1)^2+20*(B+1)^2) := Nat.add_le_add ht (Nat.add_le_add hu hlin)
      _ = _ := by ring

end Expr
end WLTime.NatCode

end OAI
