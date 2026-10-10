import OAI.Computability.WeisfeilerLeman.Transducer

namespace OAI

universe uK uA

namespace WLTime.BitWords
 def value (xs : List Bool) : ℕ := Nat.ofDigits 2 (xs.map Bool.toNat)
 @[simp] theorem value_nil : value []=0 := rfl
 @[simp] theorem value_cons (b : Bool) (xs : List Bool) : value (b::xs)=b.toNat+2*value xs := rfl
 theorem value_ofFn {w : ℕ} (f : Fin w → Bool) : value (List.ofFn f)=Nat.ofBits f := by
  induction w with
  | zero => simp [value]
  | succ w ih =>
    rw [List.ofFn_succ,value_cons,Nat.ofBits_succ,ih]
    dsimp only [Function.comp_def]
    omega
 theorem value_lt (xs : List Bool) : value xs<2^xs.length := by
  rw [←List.ofFn_get xs,value_ofFn]
  simpa only [List.length_ofFn] using Nat.ofBits_lt_two_pow xs.get
 theorem value_word {w : ℕ} (a : Word w) : value (wordBits a)=a.val := by
  rw [wordBits,value_ofFn,Nat.ofBits_testBit,Nat.mod_eq_of_lt a.isLt]
 theorem testBit_value (xs : List Bool) (i : ℕ) : (value xs).testBit i=xs.getD i false := by
  rw [←List.ofFn_get xs,value_ofFn,Nat.testBit_ofBits]
  simp only [List.ofFn_get]
  split_ifs with h
  · change xs[i]=xs.getD i false
    exact (List.getD_eq_getElem _ _ h).symm
  · exact (List.getD_eq_default xs false (Nat.le_of_not_gt h)).symm
 theorem word_of_value (xs : List Bool) : wordBits (⟨value xs,value_lt xs⟩ : Word xs.length)=xs := by
  apply List.ext_getElem
  · simp [wordBits]
  · intro i hi hj
    simp only [wordBits,List.getElem_ofFn,testBit_value]
    exact List.getD_eq_getElem _ _ hj
 def inc : List Bool → List Bool
  | [] => []
  | false::xs => true::xs
  | true::xs => false::inc xs
 @[simp] theorem length_inc (xs : List Bool) : (inc xs).length=xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [inc,ih]
 theorem inc_value (xs : List Bool) : value (inc xs)=(value xs+1)%2^xs.length := by
  induction xs with
  | nil => simp [inc]
  | cons b xs ih =>
    cases b
    · have hx := value_lt xs
      simp only [inc,value_cons,Bool.toNat_false,Bool.toNat_true,List.length_cons,pow_succ]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · simp only [inc,value_cons,Bool.toNat_false,Bool.toNat_true,List.length_cons,pow_succ,ih,zero_add]
      have he : 1+2*value xs+1=2*(value xs+1) := by omega
      rw [he,Nat.mul_comm (2^xs.length) 2,Nat.mul_mod_mul_left]
 theorem word_injective {w : ℕ} : Function.Injective (wordBits (w:=w)) := by
  intro a b h
  apply Fin.ext
  simpa only [value_word] using congrArg value h
end WLTime.BitWords

namespace WLTime.BitWords
 def carry : List Bool → ℕ
  | true::xs => carry xs+1
  | _ => 0
 def rest : List Bool → List Bool
  | true::xs => rest xs
  | xs => xs
 def raise : List Bool → List Bool
  | [] => []
  | _::xs => true::xs
 theorem carry_le (xs : List Bool) : carry xs≤xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [carry]; omega
 theorem inc_decompose (xs : List Bool) : inc xs=List.replicate (carry xs) false++raise (rest xs) := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [inc,carry,rest,raise,ih,List.replicate_succ]
end WLTime.BitWords
namespace WLTime.TypedStack.Code
open BitWords
variable {K : Type uK} [DecidableEq K]
def carryCode (a b : K) : Code K Bool :=
  .loop (fun v => v a==some true) (.seq (.pop a) (.push b false))
def raiseCode (a : K) : Code K Bool :=
  .branch (nonempty a) (.seq (.pop a) (.push a true)) .skip
def increment (a b : K) : Code K Bool :=
  .seq (carryCode a b) (.seq (raiseCode a) (.transfer b a false))
 theorem carryCode_exec (a b : K) (hab : a≠b) (s : Stacks K Bool) :
    (carryCode a b).Exec s (5*carry (s a)+1)
      (Function.update (Function.update s a (rest (s a))) b (List.replicate (carry (s a)) false++s b)) := by
  generalize hx : s a=xs
  induction xs generalizing s with
  | nil =>
    have hout : Function.update (Function.update s a (rest [])) b (List.replicate (carry []) false++s b)=s := by
      simp only [rest,carry,List.replicate_zero,List.nil_append]
      rw [←hx,Function.update_eq_self,Function.update_eq_self]
    rw [hout]
    exact .loop_false (by simp [tops,hx])
  | cons x xs ih =>
    cases x
    · have hout : Function.update (Function.update s a (rest (false::xs))) b (List.replicate (carry (false::xs)) false++s b)=s := by
        simp only [rest,carry,List.replicate_zero,List.nil_append]
        rw [←hx,Function.update_eq_self,Function.update_eq_self]
      rw [hout]
      exact .loop_false (by simp [tops,hx])
    · let mid := Function.update (Function.update s a xs) b (false::s b)
      have hb : (Code.seq (.pop a) (.push b false)).Exec s 4 mid := by
        simpa only [hx,List.tail_cons,Function.update_of_ne hab.symm,mid] using
          Exec.seq (Exec.pop s a) (Exec.push (Function.update s a (s a).tail) b false)
      have hs : mid a=xs := by simp [mid,hab]
      have hh := ih mid hs
      have hout : Function.update (Function.update mid a (rest xs)) b (List.replicate (carry xs) false++mid b)=
          Function.update (Function.update s a (rest (true::xs))) b (List.replicate (carry (true::xs)) false++s b) := by
        funext k
        by_cases hk : k=b
        · subst k
          simp only [Function.update_self,mid,carry]
          rw [List.replicate_succ']
          simp only [List.append_assoc,List.singleton_append]
        · by_cases ha : k=a
          · subst k; simp [mid,hk,rest]
          · simp [mid,hk,ha]
      rw [hout] at hh
      have he := Exec.loop_true (p:=fun v : Tops K Bool => v a==some true) (by simp [tops,hx]) hb hh
      convert he using 1
      · rfl
      · simp [carry]; omega
 theorem raiseCode_exec (a : K) (s : Stacks K Bool) :
    ∃u≤5,(raiseCode a).Exec s u (Function.update s a (raise (s a))) := by
  cases hx : s a with
  | nil =>
    refine ⟨2,by omega,?_⟩
    have ht : Function.update s a (raise (s a))=s := by rw [hx]; change Function.update s a []=s; rw [←hx]; exact Function.update_eq_self _ _
    rw [hx] at ht
    rw [ht]
    exact Exec.branch_false (by simp [nonempty,tops,hx]) (Exec.skip s)
  | cons b xs =>
    have he := Exec.seq (Exec.pop s a) (Exec.push (Function.update s a (s a).tail) a true)
    have hf := Exec.branch_true (b:=.skip) (p:=nonempty a) (by simp [nonempty,tops,hx]) he
    refine ⟨5,by omega,?_⟩
    simpa only [raiseCode,hx,List.tail_cons,Function.update_self,Function.update_idem,raise] using hf
 theorem increment_exec (a b : K) (hab : a≠b) (s : Stacks K Bool) (hb : s b=[]) :
    ∃u≤10*(s a).length+7,(increment a b).Exec s u (Function.update s a (inc (s a))) := by
  let mid := Function.update (Function.update s a (rest (s a))) b (List.replicate (carry (s a)) false)
  have hc : (carryCode a b).Exec s (5*carry (s a)+1) mid := by simpa only [hb,List.append_nil] using carryCode_exec a b hab s
  obtain ⟨u,hu,he⟩ := raiseCode_exec a mid
  have ht := transfer_exec b a hab.symm false (Function.update mid a (raise (mid a)))
  have hf := Exec.seq hc (Exec.seq he ht)
  have hout : Function.update (Function.update (Function.update mid a (raise (mid a))) b []) a
      (((Function.update mid a (raise (mid a))) b).reverse++(Function.update mid a (raise (mid a))) a)=
      Function.update s a (inc (s a)) := by
    funext k
    by_cases ha : k=a
    · subst k
      simp [mid,hab,hab.symm,inc_decompose]
    · by_cases hkb : k=b
      · subst k; simp [mid,ha,hb]
      · simp [mid,ha,hkb]
  rw [hout] at hf
  refine ⟨_,?_,hf⟩
  simp only [mid,Function.update_of_ne hab.symm,Function.update_self,List.length_replicate]
  have h := carry_le (s a)
  omega
end WLTime.TypedStack.Code

namespace WLTime.SparseMatch
open TypedStack
abbrev Reg := Fin 4
def state (a b f h : List Bool) : Stacks Reg Bool := ![a,b,f,h]
def body : Code Reg Bool :=
  .seq (.pushDyn 2 (fun v => (v 2).getD false && ((v 0).getD false == (v 1).getD false)))
    (.seq (.pushDyn 3 (fun v => (v 0).getD false)) (.seq (.pop 0) (.pop 1)))
def program : ℕ → Code Reg Bool
  | 0 => .skip
  | n+1 => .seq body (program n)
 theorem body_exec (x y q : Bool) (xs ys fs hs : List Bool) :
    body.Exec (state (x::xs) (y::ys) (q::fs) hs) 8
      (state xs ys ((q&&(x==y))::q::fs) (x::hs)) := by
  let s := state (x::xs) (y::ys) (q::fs) hs
  let s₁ := Function.update s 2 ((q&&(x==y))::q::fs)
  let s₂ := Function.update s₁ 3 (x::hs)
  let s₃ := Function.update s₂ 0 xs
  have h₁ : (Code.pushDyn 2 (fun v : Tops Reg Bool => (v 2).getD false && ((v 0).getD false == (v 1).getD false))).Exec s 2 s₁ := by
    simpa [s,s₁,state,tops] using Code.Exec.pushDyn s 2 (fun v => (v 2).getD false && ((v 0).getD false == (v 1).getD false))
  have h₂ : (Code.pushDyn 3 (fun v : Tops Reg Bool => (v 0).getD false)).Exec s₁ 2 s₂ := by
    simpa [s₂,s₁,s,state,tops] using Code.Exec.pushDyn s₁ 3 (fun v => (v 0).getD false)
  have h₃ : (Code.pop 0).Exec s₂ 2 s₃ := by simpa [s₃,s₂,s₁,s,state] using Code.Exec.pop s₂ 0
  have h₄ : (Code.pop 1).Exec s₃ 2 (state xs ys ((q&&(x==y))::q::fs) (x::hs)) := by
    have he := Code.Exec.pop s₃ 1
    convert he using 1
    funext i; fin_cases i <;> simp [s₃,s₂,s₁,s,state]
  exact Code.Exec.seq h₁ (Code.Exec.seq h₂ (Code.Exec.seq h₃ h₄))
 theorem program_exec (xs ys tail fs hs : List Bool) (q : Bool) (hlen : ys.length=xs.length) :
    ∃gs, gs.length=xs.length+fs.length+1 ∧ gs.headD false=(q && (xs==ys)) ∧
      (program xs.length).Exec (state (xs++tail) ys (q::fs) hs) (8*xs.length+1)
        (state tail [] gs (xs.reverse++hs)) := by
  induction xs generalizing ys fs hs q with
  | nil =>
    have hy : ys=[] := List.eq_nil_of_length_eq_zero hlen
    subst ys
    exact ⟨q::fs,by simp,by simp,by simpa [program,state] using Code.Exec.skip (state tail [] (q::fs) hs)⟩
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have hy : ys.length=xs.length := by simpa using hlen
      obtain ⟨gs,hg,hhead,he⟩ := ih ys (q::fs) (x::hs) (q&&(x==y)) hy
      refine ⟨gs,by simp only [List.length_cons] at hg ⊢; omega,?_,?_⟩
      · rw [hhead]
        simp only [List.cons_beq_cons]
        cases q <;> cases hxy : (x==y) <;> simp
      · have h := Code.Exec.seq (body_exec x y q (xs++tail) ys fs hs) he
        simpa only [program,List.length_cons,List.cons_append,List.reverse_cons,List.append_assoc,List.singleton_append,List.nil_append,Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
 theorem program_size (n : ℕ) : (program n).controlSize=8*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [program,body,Code.controlSize,ih]; omega
end WLTime.SparseMatch
namespace WLTime.SparseTake
open TypedStack
abbrev Reg := Fin 3
def state (a b c : List Bool) : Stacks Reg Bool := ![a,b,c]
def body : Code Reg Bool :=
  .seq (.pushDyn 1 (fun v => (v 0).getD false))
    (.seq (.pushDyn 2 (fun v => (v 0).getD false)) (.pop 0))
def program : ℕ → Code Reg Bool
  | 0 => .skip
  | n+1 => .seq body (program n)
 theorem body_exec (x : Bool) (xs bs cs : List Bool) :
    body.Exec (state (x::xs) bs cs) 6 (state xs (x::bs) (x::cs)) := by
  let s := state (x::xs) bs cs
  let s₁ := Function.update s 1 (x::bs)
  let s₂ := Function.update s₁ 2 (x::cs)
  have he₁ : (Code.pushDyn 1 (fun v : Tops Reg Bool => (v 0).getD false)).Exec s 2 s₁ := by
    simpa [s₁,s,state,tops] using Code.Exec.pushDyn s 1 (fun v => (v 0).getD false)
  have he₂ : (Code.pushDyn 2 (fun v : Tops Reg Bool => (v 0).getD false)).Exec s₁ 2 s₂ := by
    simpa [s₂,s₁,s,state,tops] using Code.Exec.pushDyn s₁ 2 (fun v => (v 0).getD false)
  have he₃ : (Code.pop 0).Exec s₂ 2 (state xs (x::bs) (x::cs)) := by
    have he := Code.Exec.pop s₂ 0
    convert he using 1
    funext i; fin_cases i <;> simp [s₂,s₁,s,state]
  exact Code.Exec.seq he₁ (Code.Exec.seq he₂ he₃)
 theorem program_exec (xs tail bs cs : List Bool) :
    (program xs.length).Exec (state (xs++tail) bs cs) (6*xs.length+1)
      (state tail (xs.reverse++bs) (xs.reverse++cs)) := by
  induction xs generalizing bs cs with
  | nil => simpa [program,state] using Code.Exec.skip (state tail bs cs)
  | cons x xs ih =>
    have he := Code.Exec.seq (body_exec x (xs++tail) bs cs) (ih (x::bs) (x::cs))
    simpa only [program,List.length_cons,List.cons_append,List.reverse_cons,List.append_assoc,List.singleton_append,List.nil_append,Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he
 theorem program_size (n : ℕ) : (program n).controlSize=6*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [program,body,Code.controlSize,ih]; omega
end WLTime.SparseTake

namespace WLTime.SparseLookup
open TypedStack
abbrev Reg := Fin 8
def state (log query out hist copy flags candidate tmp : List Bool) : Stacks Reg Bool :=
  ![log,query,out,hist,copy,flags,candidate,tmp]
def matchMap : Fin 4 → Reg := ![0,4,5,3]
def takeMap : Fin 3 → Reg := ![0,3,6]
 theorem matchMap_inj : Function.Injective matchMap := by decide
 theorem takeMap_inj : Function.Injective takeMap := by decide
def first (w : ℕ) : Code Reg Bool :=
  .seq (.copy 1 4 7 false) (.seq (.push 5 true)
    (.seq ((SparseMatch.program w).relabel matchMap) ((SparseTake.program w).relabel takeMap)))
def finish : Code Reg Bool :=
  .seq (.branch (fun v => (v 5).getD false) (.transfer 6 2 false) (.clear 6)) (.clear 5)
def one (w : ℕ) : Code Reg Bool := .seq (first w) finish
 theorem first_exec (key value query tail hist : List Bool)
    (hk : key.length=query.length) (hv : value.length=query.length) :
    ∃fs, fs.length=query.length+1 ∧ fs.headD false=(key==query) ∧
      (first query.length).Exec (state (key++value++tail) query [] hist [] [] [] [])
        (26*query.length+6)
        (state tail query [] (value.reverse++key.reverse++hist) [] fs value.reverse []) := by
  let s₀ := state (key++value++tail) query [] hist [] [] [] []
  let s₁ := state (key++value++tail) query [] hist query [] [] []
  let s₂ := state (key++value++tail) query [] hist query [true] [] []
  have h₁ : (Code.copy 1 4 7 false).Exec s₀ (12*query.length+2) s₁ := by
    have h := Code.copy_exec (1 : Reg) 4 7 (by decide) (by decide) (by decide) false s₀ rfl
    convert h using 1
    · rfl
    · funext i; fin_cases i <;> simp [s₁,s₀,state]
  have h₂ : (Code.push 5 true).Exec s₁ 2 s₂ := by
    have h := Code.Exec.push s₁ 5 true
    convert h using 1
    funext i; fin_cases i <;> simp [s₂,s₁,state]
  obtain ⟨fs,hlen,hhead,hm⟩ := SparseMatch.program_exec key query (value++tail) [] hist true hk.symm
  have h₃ : ((SparseMatch.program query.length).relabel matchMap).Exec s₂ (8*query.length+1)
      (state (value++tail) query [] (key.reverse++hist) [] fs [] []) := by
    rw [hk] at hm
    apply Code.relabel_exec_of_maps matchMap matchMap_inj hm
    · intro i; fin_cases i <;> simp [s₂,state,SparseMatch.state,matchMap,List.append_assoc]
    · intro i; fin_cases i <;> simp [state,SparseMatch.state,matchMap]
    · intro i hi; fin_cases i <;> simp_all [state,s₂,matchMap]
      <;> first | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | exact False.elim (hi 3 rfl)
  have h₄ : ((SparseTake.program query.length).relabel takeMap).Exec
      (state (value++tail) query [] (key.reverse++hist) [] fs [] []) (6*query.length+1)
      (state tail query [] (value.reverse++key.reverse++hist) [] fs value.reverse []) := by
    have ht := SparseTake.program_exec value tail (key.reverse++hist) []
    rw [hv] at ht
    apply Code.relabel_exec_of_maps takeMap takeMap_inj ht
    · intro i; fin_cases i <;> simp [state,SparseTake.state,takeMap]
    · intro i; fin_cases i <;> simp [state,SparseTake.state,takeMap,List.append_assoc]
    · intro i hi; fin_cases i <;> simp_all [state,takeMap]
      <;> first | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl)
  refine ⟨fs,by simpa [hk] using hlen,by simpa using hhead,?_⟩
  have he := Code.Exec.seq h₁ (Code.Exec.seq h₂ (Code.Exec.seq h₃ h₄))
  convert he using 1
  · rfl
  · omega
 theorem finish_exec (tail query hist fs value : List Bool) :
    ∃u ≤ 5*value.length+3*fs.length+3,
      finish.Exec (state tail query [] hist [] fs value.reverse []) u
        (state tail query (if fs.headD false then value else []) hist [] [] [] []) := by
  let s := state tail query [] hist [] fs value.reverse []
  let out := if fs.headD false then value else []
  let mid := state tail query out hist [] fs [] []
  have hb : ∃u ≤ 5*value.length+2,
      (Code.branch (fun v : Tops Reg Bool => (v 5).getD false) (.transfer 6 2 false) (.clear 6)).Exec s u mid := by
    cases hh : fs.headD false
    · have he := Code.clear_exec (6 : Reg) s
      have ho : out=[] := ite_eq_right (by rw [hh]; decide)
      have hm : Function.update s 6 []=mid := by
        funext i; fin_cases i <;> simp [s,mid,state,ho]
      rw [hm] at he
      refine ⟨_,?_,Code.Exec.branch_false (by simpa [tops,s,state] using hh) he⟩
      simp [s,state]; omega
    · have he := Code.transfer_exec (6 : Reg) 2 (by decide) false s
      have ho : out=value := ite_eq_left hh
      have hm : Function.update (Function.update s 6 []) 2 ((s 6).reverse++s 2)=mid := by
        funext i; fin_cases i <;> simp [s,mid,state,ho]
      rw [hm] at he
      refine ⟨_,?_,Code.Exec.branch_true (by simpa [tops,s,state] using hh) he⟩
      simp [s,state]
  obtain ⟨u,hu,he⟩ := hb
  have hc := Code.clear_exec (5 : Reg) mid
  have hf : Function.update mid 5 []=state tail query out hist [] [] [] [] := by
    funext i; fin_cases i <;> simp [mid,state]
  rw [hf] at hc
  refine ⟨_,?_,Code.Exec.seq he hc⟩
  change u+(3*fs.length+1) ≤ _
  omega
 theorem one_exec (key value query tail hist : List Bool)
    (hk : key.length=query.length) (hv : value.length=query.length) :
    ∃u ≤ 40*(query.length+1),
      (one query.length).Exec (state (key++value++tail) query [] hist [] [] [] []) u
        (state tail query (if key=query then value else []) (value.reverse++key.reverse++hist) [] [] [] []) := by
  obtain ⟨fs,hf,hh,he⟩ := first_exec key value query tail hist hk hv
  obtain ⟨u,hu,hg⟩ := finish_exec tail query (value.reverse++key.reverse++hist) fs value
  rw [hh] at hg
  simp only [beq_iff_eq] at hg
  refine ⟨_,?_,Code.Exec.seq he hg⟩
  rw [hf,hv] at hu
  omega
end WLTime.SparseLookup
namespace WLTime.TypedStack.Code
variable {K : Type uK} {A : Type uA} [DecidableEq K]
def pushList (k : K) : List A → Code K A
  | [] => .skip
  | x::xs => .seq (pushList k xs) (.push k x)
 theorem pushList_exec (k : K) (xs : List A) (s : Stacks K A) :
    (pushList k xs).Exec s (2*xs.length+1) (Function.update s k (xs++s k)) := by
  induction xs with
  | nil => simpa [pushList] using Exec.skip s
  | cons x xs ih =>
    have he := Exec.seq ih (Exec.push (Function.update s k (xs++s k)) k x)
    simpa only [pushList,List.length_cons,List.cons_append,Function.update_self,Function.update_idem,
      Nat.mul_add,Nat.mul_one,Nat.add_assoc] using he
 omit [DecidableEq K] in
 theorem pushList_size (k : K) (xs : List A) : (pushList k xs).controlSize=2*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [pushList,controlSize,List.length_cons,ih]; omega
end WLTime.TypedStack.Code
namespace WLTime.SparseLookup
open TypedStack
abbrev Entry := List Bool × List Bool
def flatten (l : List Entry) : List Bool := l.flatMap (fun e => e.1++e.2)
def WellFormed (w : ℕ) (l : List Entry) : Prop := ∀e∈l,e.1.length=w ∧ e.2.length=w
def consumed (q : List Bool) : List Entry → List Entry
  | [] => []
  | e::l => if e.1=q then [e] else e::consumed q l
def remaining (q : List Bool) : List Entry → List Entry
  | [] => []
  | e::l => if e.1=q then l else remaining q l
def found (q : List Bool) : List Entry → List Bool
  | [] => []
  | e::l => if e.1=q then e.2 else found q l
 theorem split_log (q : List Bool) (l : List Entry) : consumed q l++remaining q l=l := by
  induction l with
  | nil => rfl
  | cons e l ih => by_cases he : e.1=q <;> simp [consumed,remaining,he,ih]
 theorem flatten_append (l m : List Entry) : flatten (l++m)=flatten l++flatten m := by simp [flatten]
 theorem flatten_length (w : ℕ) (l : List Entry) (hw : WellFormed w l) : (flatten l).length=2*w*l.length := by
  induction l with
  | nil => simp [flatten]
  | cons e l ih =>
    have he := hw e (by simp)
    have hl : WellFormed w l := fun a ha => hw a (by simp [ha])
    have hh := ih hl
    simp only [flatten,List.flatMap_cons,List.length_append,List.length_cons] at *
    rw [he.1,he.2,hh]
    ring
 theorem consumed_length (q : List Bool) (l : List Entry) : (flatten (consumed q l)).length ≤ (flatten l).length := by
  have hh := congrArg (fun l => (flatten l).length) (split_log q l)
  rw [flatten_append,List.length_append] at hh
  omega
 theorem found_length (q : List Bool) (l : List Entry) (hw : WellFormed q.length l) :
    (found q l).length=0 ∨ (found q l).length=q.length := by
  induction l with
  | nil => exact Or.inl rfl
  | cons e l ih =>
    by_cases he : e.1=q
    · exact Or.inr (by simpa [found,he] using (hw e (by simp)).2)
    · simpa [found,he] using ih (fun a ha => hw a (by simp [ha]))
def keepGoing (v : Tops Reg Bool) : Bool := (Code.nonempty 0 v) && !(Code.nonempty 2 v)
def search (w : ℕ) : Code Reg Bool := .loop keepGoing (one w)
 theorem search_exec (q : List Bool) (l : List Entry) (hist : List Bool) (hq : 0<q.length) (hw : WellFormed q.length l) :
    ∃u ≤ 42*(q.length+1)*l.length+1,
      (search q.length).Exec (state (flatten l) q [] hist [] [] [] []) u
        (state (flatten (remaining q l)) q (found q l) ((flatten (consumed q l)).reverse++hist) [] [] [] []) := by
  induction l generalizing hist with
  | nil =>
    refine ⟨1,by simp,?_⟩
    have he : (search q.length).Exec (state [] q [] hist [] [] [] []) 1 (state [] q [] hist [] [] [] []) :=
      Code.Exec.loop_false (by simp [keepGoing,Code.nonempty,tops,state])
    simpa [flatten,consumed,remaining,found] using he
  | cons e l ih =>
    have he := hw e (by simp)
    have hl : WellFormed q.length l := fun a ha => hw a (by simp [ha])
    have hkne : e.1≠[] := by
      intro h
      have hh := he.1
      rw [h,List.length_nil] at hh
      omega
    obtain ⟨a,ha,hstep⟩ := one_exec e.1 e.2 q (flatten l) hist he.1 he.2
    by_cases h : e.1=q
    · have hval : e.2≠[] := by intro hh; rw [hh,List.length_nil] at he; omega
      simp only [ite_eq_left h] at hstep
      have hstop : (search q.length).Exec
          (state (flatten l) q e.2 (e.2.reverse++e.1.reverse++hist) [] [] [] []) 1
          (state (flatten l) q e.2 (e.2.reverse++e.1.reverse++hist) [] [] [] []) :=
        Code.Exec.loop_false (by simp [keepGoing,Code.nonempty,tops,state,hval])
      have hex := Code.Exec.loop_true (p:=keepGoing) (by simp [keepGoing,Code.nonempty,tops,state,hkne]) hstep hstop
      refine ⟨a+1+1,?_,?_⟩
      · simp only [List.length_cons]; nlinarith
      · simpa only [search,flatten,List.flatMap_cons,consumed,remaining,found,ite_eq_left h,List.flatMap_nil,List.append_nil,
          List.reverse_append,List.append_assoc] using hex
    · simp only [ite_eq_right h] at hstep
      obtain ⟨b,hb,hrest⟩ := ih (e.2.reverse++e.1.reverse++hist) hl
      have hex := Code.Exec.loop_true (p:=keepGoing) (by simp [keepGoing,Code.nonempty,tops,state,hkne]) hstep hrest
      refine ⟨a+b+1,?_,?_⟩
      · simp only [List.length_cons]; nlinarith
      · simpa only [search,flatten,List.flatMap_cons,consumed,remaining,found,ite_eq_right h,List.reverse_append,List.append_assoc] using hex
end WLTime.SparseLookup

end OAI
