import OAI.Computability.Scheduling.StackMachine

namespace OAI

section

namespace ThreeMachine.StackCompiler

inductive Data
  | nil
  | pair (head tail : Data)
  deriving DecidableEq

namespace Data

def encode : Data → List Bool
  | .nil => [false]
  | .pair a b => true :: a.encode ++ b.encode

def size (d : Data) : ℕ := d.encode.length

@[simp] theorem encode_nil : encode nil = [false] := rfl
@[simp] theorem encode_pair (a b : Data) : encode (pair a b) = true :: a.encode ++ b.encode := rfl
@[simp] theorem size_nil : size nil = 1 := rfl
@[simp] theorem size_pair (a b : Data) : size (pair a b) = a.size + b.size + 1 := by
  simp [size,encode,Nat.add_comm]

def head : Data → Data | .nil => .nil | .pair a _ => a
def tail : Data → Data | .nil => .nil | .pair _ b => b

end Data

namespace Program
variable {k : ℕ}

def scanActions (src dst ct : Fin (k+1)) (h : Heads k) : Actions k := fun i =>
  if i = src then .pop else if i = dst then .push ((h src).getD false)
  else if i = ct then if (h src).getD false then .push true else .pop else .stay

def scan (src dst ct : Fin (k+1)) : Program k (Option Bool) :=
  loop (fun h => (h ct).isSome) (instruction (scanActions src dst ct))

def scanned (src dst ct : Fin (k+1)) (s : Store k) (rest word : List Bool) (c : ℕ) : Store k :=
  Function.update (Function.update (Function.update s src rest) dst (word.reverse ++ s dst))
    ct (List.replicate c true)

def scanOnce (src dst ct : Fin (k+1)) (s : Store k) (b : Bool) (rest : List Bool) : Store k :=
  Function.update (Function.update (Function.update s src rest) dst (b :: s dst))
    ct (if b then true :: s ct else (s ct).tail)

theorem scan_instruction {src dst ct : Fin (k+1)}
    (h₁ : src ≠ dst) (h₂ : src ≠ ct) (h₃ : dst ≠ ct)
    (s : Store k) (b : Bool) (rest : List Bool) (hs : s src = b :: rest) :
    Exec (instruction (scanActions src dst ct)) ⟨false,s⟩ 1 ⟨true,scanOnce src dst ct s b rest⟩ := by
  convert instruction_exec (scanActions src dst ct) s using 1
  congr 1
  funext i
  by_cases hi : i = ct
  · subst i; cases b <;> simp [scanActions,scanOnce,hs,h₂.symm,h₃.symm,Action.apply]
  · by_cases hd : i = dst
    · subst i; simp [scanActions,scanOnce,hs,hi,h₁.symm,Action.apply]
    · by_cases hsrc : i = src
      · subst i; simp [scanActions,scanOnce,hs,h₁,h₂,Action.apply]
      · simp [scanActions,scanOnce,hi,hd,hsrc,Action.apply]

theorem scanned_scanned {src dst ct : Fin (k+1)}
    (h₃ : dst ≠ ct) (s : Store k) (rest mid w₁ w₂ : List Bool) (c d : ℕ) :
    scanned src dst ct (scanned src dst ct s mid w₁ d) rest w₂ c =
      scanned src dst ct s rest (w₁ ++ w₂) c := by
  funext i
  by_cases hc : i = ct
  · subst i; simp [scanned]
  · by_cases hd : i = dst
    · subst i; simp [scanned,h₃,List.reverse_append,List.append_assoc]
    · by_cases hs : i = src
      · subst i; simp [scanned,hc,hd]
      · simp [scanned,hc,hd,hs]

theorem scan_tree_continue {src dst ct : Fin (k+1)}
    (h₁ : src ≠ dst) (h₂ : src ≠ ct) (h₃ : dst ≠ ct) (d : Data) :
    ∀ (s t : Store k) (rest : List Bool) (c m : ℕ),
      s src = d.encode ++ rest → s ct = List.replicate (c+1) true →
      Exec (scan src dst ct) ⟨none,scanned src dst ct s rest d.encode c⟩ m ⟨none,t⟩ →
      Exec (scan src dst ct) ⟨none,s⟩ (3*d.size+m) ⟨none,t⟩ := by
  induction d with
  | nil =>
    intro s t rest c m hs hc hrest
    have hsrc : s src = false :: rest := by simpa using hs
    have he : scanOnce src dst ct s false rest = scanned src dst ct s rest [false] c := by
      simp [scanOnce,scanned,hc,List.replicate_succ]
    have hbody := scan_instruction h₁ h₂ h₃ s false rest hsrc
    rw [he] at hbody
    have hx := loop_iterate (fun h => (h ct).isSome) (by simp [hc,List.replicate_succ]) hbody hrest
    convert hx using 1 <;> first | rfl | simp only [Data.size_nil]; omega
  | pair a b iha ihb =>
    intro s t rest c m hs hc hrest
    let s₁ := scanOnce src dst ct s true (a.encode ++ b.encode ++ rest)
    have hs₁ : s₁ src = a.encode ++ (b.encode ++ rest) := by
      simp [s₁,scanOnce,h₁,h₂,List.append_assoc]
    have hc₁ : s₁ ct = List.replicate (c+2) true := by
      simp [s₁,scanOnce,hc,List.replicate_succ]
    let s₂ := scanned src dst ct s₁ (b.encode ++ rest) a.encode (c+1)
    have hs₂ : s₂ src = b.encode ++ rest := by simp [s₂,scanned,h₁,h₂]
    have hc₂ : s₂ ct = List.replicate (c+1) true := by simp [s₂,scanned]
    have hend : scanned src dst ct s₂ rest b.encode c =
        scanned src dst ct s rest (Data.pair a b).encode c := by
      rw [show s₂ = scanned src dst ct s₁ (b.encode ++ rest) a.encode (c+1) by rfl,
        scanned_scanned h₃]
      funext i
      by_cases hi : i = ct
      · subst i; simp [scanned]
      · by_cases hd : i = dst
        · subst i; simp [scanned,s₁,scanOnce,h₃,List.reverse_cons,List.reverse_append,
            Data.encode,List.append_assoc]
        · by_cases hsrc : i = src
          · subst i; simp [scanned,hi,hd]
          · simp [scanned,s₁,scanOnce,hi,hd,hsrc]
    have hafterB := ihb s₂ t rest c m hs₂ hc₂ (by rwa [hend])
    have hafterA := iha s₁ t (b.encode ++ rest) (c+1) (3*b.size+m) hs₁ hc₁ hafterB
    have hsrc : s src = true :: (a.encode ++ b.encode ++ rest) := by
      simpa [Data.encode,List.append_assoc] using hs
    have hbody := scan_instruction h₁ h₂ h₃ s true _ hsrc
    have hx := loop_iterate (fun h => (h ct).isSome) (by simp [hc,List.replicate_succ]) hbody hafterA
    convert hx using 1 <;> first | rfl | rw [Data.size_pair]; omega

theorem scan_tree {src dst ct : Fin (k+1)}
    (h₁ : src ≠ dst) (h₂ : src ≠ ct) (h₃ : dst ≠ ct)
    (d : Data) (s : Store k) (rest : List Bool)
    (hs : s src = d.encode ++ rest) (hc : s ct = [true]) :
    Exec (scan src dst ct) ⟨none,s⟩ (3*d.size)
      ⟨none,scanned src dst ct s rest d.encode 0⟩ := by
  have hstop : Exec (scan src dst ct) ⟨none,scanned src dst ct s rest d.encode 0⟩ 0
      ⟨none,scanned src dst ct s rest d.encode 0⟩ :=
    loop_stop _ _ _ (by simp [scanned])
  simpa using scan_tree_continue h₁ h₂ h₃ d s _ rest 0 0 hs (by simpa using hc) hstop

end Program
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Program
variable {k : ℕ} {Q R : Type}

def Runs (P : Program k Q) (s t : Store k) (bound : ℕ) : Prop :=
  ∃ n ≤ bound, ∃ q, Exec P ⟨P.initial,s⟩ n ⟨q,t⟩

theorem Exec.runs {P : Program k Q} {s t : Store k} {n : ℕ} {q : Q}
    (h : Exec P ⟨P.initial,s⟩ n ⟨q,t⟩) : P.Runs s t n := ⟨n,le_rfl,q,h⟩

theorem Runs.mono {P : Program k Q} {s t : Store k} {n m : ℕ}
    (h : P.Runs s t n) (hnm : n ≤ m) : P.Runs s t m := by
  obtain ⟨t',ht',q,hq⟩ := h
  exact ⟨t',ht'.trans hnm,q,hq⟩

theorem Runs.computes {P : Program k Q} {s t : Store k} {n : ℕ}
    (h : P.Runs s t n) : P.Computes s t n := by
  obtain ⟨m,hm,q,hq⟩ := h
  refine ⟨m,hm,?_,?_⟩
  · exact congrArg State.store hq.iterate
  · unfold run
    rw [hq.iterate]
    exact hq.halted

theorem Runs.seq {P : Program k Q} {P' : Program k R} {s t u : Store k} {n m : ℕ}
    (h : P.Runs s t n) (h' : P'.Runs t u m) : (seq P P').Runs s u (n+m+1) := by
  obtain ⟨n',hn',q,hq⟩ := h
  obtain ⟨m',hm',r,hr⟩ := h'
  exact (seq_exec hq hr).runs.mono (by omega)

def branch (test : Heads k → Bool) (P : Program k Q) (P' : Program k R) :
    Program k (Option (Q ⊕ R)) where
  initial := none
  transition q h := match q with
    | none => some (some (if test h then .inl P.initial else .inr P'.initial),stayActions)
    | some (.inl q) => (P.transition q h).map (fun qa => (some (.inl qa.1),qa.2))
    | some (.inr q) => (P'.transition q h).map (fun qa => (some (.inr qa.1),qa.2))

theorem branch_left_exec (test : Heads k → Bool) {P : Program k Q} (P' : Program k R)
    {s t : State k Q} {n : ℕ} (h : Exec P s n t) :
    Exec (branch test P P') (State.mapControl (some ∘ Sum.inl) s) n
      (State.mapControl (some ∘ Sum.inl) t) := by
  induction h with
  | halt he =>
    apply Exec.halt
    unfold step at he ⊢
    cases hh : P.transition s.control (fun i => (s.store i).head?) <;>
      simp_all [branch,State.mapControl]
  | next he _ ih =>
    apply Exec.next _ ih
    apply lift_step P (branch test P P') (some ∘ Sum.inl) _ _ _ he
    intro q heads q' a ha
    simp [branch,ha]

theorem branch_right_exec (test : Heads k → Bool) (P : Program k Q) {P' : Program k R}
    {s t : State k R} {n : ℕ} (h : Exec P' s n t) :
    Exec (branch test P P') (State.mapControl (some ∘ Sum.inr) s) n
      (State.mapControl (some ∘ Sum.inr) t) := by
  induction h with
  | halt he =>
    apply Exec.halt
    unfold step at he ⊢
    cases hh : P'.transition s.control (fun i => (s.store i).head?) <;>
      simp_all [branch,State.mapControl]
  | next he _ ih =>
    apply Exec.next _ ih
    apply lift_step P' (branch test P P') (some ∘ Sum.inr) _ _ _ he
    intro q heads q' a ha
    simp [branch,ha]

theorem Runs.branch_left (test : Heads k → Bool) {P : Program k Q} (P' : Program k R)
    {s t : Store k} {n : ℕ} (h : P.Runs s t n) (ht : test (fun i => (s i).head?) = true) :
    (branch test P P').Runs s t (n+1) := by
  obtain ⟨m,hm,q,hq⟩ := h
  have hs : (branch test P P').step ⟨none,s⟩ = some ⟨some (.inl P.initial),s⟩ := by
    simp [step,branch,ht,stayActions,Action.apply]
  exact ⟨m+1,by omega,some (.inl q),Exec.next hs (branch_left_exec test P' hq)⟩

theorem Runs.branch_right (test : Heads k → Bool) (P : Program k Q) {P' : Program k R}
    {s t : Store k} {n : ℕ} (h : P'.Runs s t n) (ht : test (fun i => (s i).head?) = false) :
    (branch test P P').Runs s t (n+1) := by
  obtain ⟨m,hm,q,hq⟩ := h
  have hs : (branch test P P').step ⟨none,s⟩ = some ⟨some (.inr P'.initial),s⟩ := by
    simp [step,branch,ht,stayActions,Action.apply]
  exact ⟨m+1,by omega,some (.inr q),Exec.next hs (branch_right_exec test P hq)⟩

def move (src dst tmp : Fin (k+1)) : Program k (Option Bool ⊕ (Option Bool ⊕ Option Bool)) :=
  seq (clear dst) (seq (transfer src tmp) (transfer tmp dst))

theorem move_exec {src dst tmp : Fin (k+1)}
    (h₁ : src ≠ dst) (h₂ : src ≠ tmp) (h₃ : dst ≠ tmp)
    (s : Store k) (htmp : s tmp = []) :
    Exec (move src dst tmp) ⟨(move src dst tmp).initial,s⟩
      (3*(s dst).length+6*(s src).length+2)
      ⟨Sum.inr (Sum.inr none),Function.update (Function.update s src []) dst (s src)⟩ := by
  let s₁ := Function.update s dst []
  let s₂ := transferResult src tmp s₁
  have hx := seq_exec (clear_exec dst s)
    (seq_exec (transfer_exec h₂ s₁) (transfer_exec h₃.symm s₂))
  have hl₁ : s₁ src = s src := by simp [s₁,h₁]
  have hl₂ : (s₂ tmp).length = (s src).length := by simp [s₂,s₁,transferResult,h₁,h₃.symm,htmp]
  have he : transferResult tmp dst s₂ = Function.update (Function.update s src []) dst (s src) := by
    funext i
    by_cases hd : i = dst
    · subst i; simp [transferResult,s₂,s₁,h₃,h₃.symm,htmp,h₁,h₁.symm]
    · by_cases ht : i = tmp
      · subst i; simp [transferResult,s₂,s₁,h₃.symm,htmp,h₁,h₂.symm]
      · by_cases hsrc : i = src
        · subst i; simp [transferResult,s₂,s₁,h₁,h₂]
        · simp [transferResult,s₂,s₁,hd,ht,hsrc]
  rw [he,hl₁,hl₂] at hx
  convert hx using 1 <;> first | rfl | omega

end ThreeMachine.StackCompiler.Program

namespace ThreeMachine.StackCompiler.Program
variable {k : ℕ}

def push (dst : Fin (k+1)) (b : Bool) : Program k Bool :=
  instruction (fun _ i => if i = dst then .push b else .stay)

theorem push_exec (dst : Fin (k+1)) (b : Bool) (s : Store k) :
    Exec (push dst b) ⟨false,s⟩ 1 ⟨true,Function.update s dst (b :: s dst)⟩ := by
  have he : (fun i => (if i = dst then Action.push b else Action.stay).apply (s i)) =
      Function.update s dst (b :: s dst) := by
    funext i
    by_cases hi : i = dst <;> simp [hi,Action.apply]
  simpa only [push,he] using instruction_exec (fun _ i => if i = dst then .push b else .stay) s

def setNil (dst : Fin (k+1)) := seq (clear dst) (push dst false)

theorem setNil_runs (dst : Fin (k+1)) (s : Store k) :
    (setNil dst).Runs s (Function.update s dst Data.nil.encode) (3*(s dst).length+2) := by
  have h := (clear_exec dst s).runs.seq (push_exec dst false (Function.update s dst [])).runs
  simpa [setNil] using h

def setPair (dst a b tmp buf : Fin (k+1)) :=
  seq (prepend b tmp buf) (seq (prepend a tmp buf)
    (seq (push tmp true) (move tmp dst buf)))

theorem setPair_runs {dst a b tmp buf : Fin (k+1)}
    (hd : dst ≠ tmp) (hd' : dst ≠ buf) (ha : a ≠ tmp) (ha' : a ≠ buf)
    (hb : b ≠ tmp) (hb' : b ≠ buf) (htb : tmp ≠ buf)
    (s : Store k) (ht : s tmp = []) (hu : s buf = []) :
    (setPair dst a b tmp buf).Runs s
      (Function.update s dst (true :: (s a ++ s b)))
      (12*(s a).length+12*(s b).length+3*(s dst).length+14) := by
  let s₁ := Function.update s tmp (s b)
  let s₂ := Function.update s tmp (s a ++ s b)
  let s₃ := Function.update s tmp (true :: (s a ++ s b))
  have h₁ : (prepend b tmp buf).Runs s s₁ (6*(s b).length+1) := by
    simpa [s₁,ht] using (prepend_exec hb hb' htb s hu).runs
  have h₂ : (prepend a tmp buf).Runs s₁ s₂ (6*(s a).length+1) := by
    have hh := (prepend_exec ha ha' htb s₁ (by simp [s₁,htb.symm,hu])).runs
    simpa [s₁,s₂,ha] using hh
  have h₃ : (push tmp true).Runs s₂ s₃ 1 := by
    simpa [s₂,s₃] using (push_exec tmp true s₂).runs
  have h₄ : (move tmp dst buf).Runs s₃ (Function.update s dst (true :: (s a ++ s b)))
      (3*(s dst).length+6*((s a).length+(s b).length+1)+2) := by
    have hh := (move_exec hd.symm htb hd' s₃ (by simp [s₃,htb.symm,hu])).runs
    have he : Function.update s₃ tmp [] = s := by
      ext i
      by_cases hi : i = tmp <;> simp [s₃,hi,ht]
    rw [he] at hh
    simpa [s₃,hd] using hh
  exact (h₁.seq (h₂.seq (h₃.seq h₄))).mono (by omega)

end ThreeMachine.StackCompiler.Program

end

end OAI
