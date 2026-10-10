import OAI.Computability.MeanPayoff.StackMacros

namespace OAI

section

namespace MeanPayoff.ForestMachine
open BinaryData (Data)
open RegisterBits
open BinaryStack (applyOp)

@[simp] theorem scratch_clear {K : ℕ} (s : Fin K → List Data) :
    Function.update (bitStore s) (⟨K, by omega⟩ : Fin (K+2)) [] = bitStore s := by
  exact Function.update_eq_self_iff.mpr (bitStore_scratch₀ s).symm

theorem boundary_contract {K : ℕ} (P : Program K) (q : Fin P.nodes) (s : Fin K → List Data)
    (h : ValidOp (P.code q) s) (out : List Bool) (bit : Bool) :
    RegisterBits.step (compile P)
      (Flow.edge (flow P) q (bitStore (afterBlock (P.code q) s)) out) bit =
      embed P (step P ⟨some q, s, out⟩ bit) := by
  change RegisterBits.step (Flow.compile (flow P)) _ _ = _
  rw [Flow.step_boundary]
  cases hop : P.code q with
  | nil i r =>
    simp [flow, hop, branch, read, afterBlock, step, embed, Flow.state,
      bitStore_update, applyOp, BinaryData.encode, Option.map] ; rfl
  | join i r =>
    have hv : 2 ≤ (s i).length := by simpa [ValidOp, hop] using h
    cases hs : s i with
    | nil => simp [hs] at hv
    | cons a xs =>
      cases xs with
      | nil => simp [hs] at hv
      | cons b xs => simp [flow, hop, branch, read, afterBlock, step, embed, Flow.state,
          bitStore_update, applyOp, hs, BinaryData.encode, List.append_assoc, Option.map] ; rfl
  | split i e n p =>
    cases hs : s i with
    | nil =>
      have hu : Function.update (bitStore s) (i.castAdd 2) [] = bitStore s :=
        Function.update_eq_self_iff.mpr (by simp [hs])
      simp [flow, hop, branch, read, afterBlock, step, embed, Flow.state,
        applyOp, hs, hu, Option.map] ; rfl
    | cons a xs =>
      cases a <;> simp [flow, hop, branch, read, afterBlock, step, embed, Flow.state,
        bitStore_update, applyOp, hs, BinaryData.encode, List.append_assoc, Option.map] <;> rfl
  | move i j hij r =>
    have hv : s i ≠ [] := by simpa [ValidOp, hop] using h
    cases hs : s i with
    | nil => exact False.elim (hv hs)
    | cons a xs => simp [flow, hop, branch, read, afterBlock, step, embed, Flow.state,
        applyOp, hs, Option.map] ; rfl
  | copy i j hij r =>
    have hv : s i ≠ [] := by simpa [ValidOp, hop] using h
    cases hs : s i with
    | nil => exact False.elim (hv hs)
    | cons a xs => simp [flow, hop, branch, read, afterBlock, step, embed, Flow.state,
        applyOp, hs, Option.map] ; rfl
  | emit b r => simp [flow, hop, branch, read, afterBlock, step, embed, Flow.state, applyOp, Option.map] ; rfl
  | coin z o => simp [flow, hop, branch, read, afterBlock, step, embed, Flow.state, applyOp, Option.map] ; rfl
  | halt => simp [flow, hop, branch, read, afterBlock, step, embed, Option.map] ; rfl

theorem one_step {K : ℕ} (P : Program K) (q : Fin P.nodes) (s : Fin K → List Data)
    (h : ValidOp (P.code q) s) (out : List Bool) (bits : ℕ → Bool) :
    advance (compile P) bits (embed P ⟨some q, s, out⟩) (duration (P.code q) s + 1) =
      embed P (step P ⟨some q, s, out⟩ (bits (duration (P.code q) s))) := by
  change RegisterBits.step (compile P)
    (advance (compile P) bits (Flow.state (flow P) q (bitStore s) out) (duration (P.code q) s)) _ = _
  rw [macro_boundary P q s h out bits, boundary_contract P q s h out]

end MeanPayoff.ForestMachine
namespace MeanPayoff.ForestMachine
open BinaryData (Data)
open RegisterBits RandomTree

def size {K : ℕ} (s : Fin K → List Data) : ℕ := ∑ i, (encodeForest (s i)).length

theorem member_size {K : ℕ} (s : Fin K → List Data) (i : Fin K) :
    (encodeForest (s i)).length ≤ size s := by
  exact Finset.single_le_sum (f := fun j => (encodeForest (s j)).length)
    (fun j _ => Nat.zero_le _) (Finset.mem_univ i)

theorem blockBound_le {K N : ℕ} (op : Instruction K N) (s : Fin K → List Data) :
    blockBound op s ≤ 7 * size s + 3 := by
  cases op with
  | move i j hij r | copy i j hij r =>
    have hm := member_size s i
    cases hs : s i with
    | nil => simp [blockBound, hs]
    | cons a xs =>
      simp only [hs, encodeForest_cons, List.length_append] at hm
      simp only [blockBound, hs]
      omega
  | nil i r | join i r | split i e n p | emit b r | coin z o | halt => simp [blockBound]

noncomputable def clock {K : ℕ} (P : Program K) (c : Config P) : ℕ :=
  match c.control with
  | none => 1
  | some q => duration (P.code q) c.store + 1

theorem clock_pos {K : ℕ} (P : Program K) (c : Config P) : 0 < clock P c := by
  unfold clock; split <;> omega

theorem clock_bound {K : ℕ} (P : Program K) (c : Config P) (h : Valid P c) :
    clock P c ≤ 7 * size c.store + 4 := by
  cases hc : c.control with
  | none => simp [clock, hc]
  | some q =>
    have hv : ValidOp (P.code q) c.store := by
      cases hop : P.code q <;> simp only [Valid, hc, ValidOp, hop] at h ⊢ <;> exact h
    have hd := (duration_spec (P.code q) c.store hv c.output (fun _ => false)).1
    have hb := blockBound_le (P.code q) c.store
    simp only [clock, hc]
    omega

theorem clock_simulation {K : ℕ} (P : Program K) (c : Config P) (h : Valid P c)
    (bits : ℕ → Bool) :
    advance (compile P) bits (embed P c) (clock P c) =
      embed P (step P c (bits (clock P c - 1))) := by
  rcases c with ⟨q, s, out⟩
  cases q with
  | none => simp [clock, embed, advance, RegisterBits.step, step, Option.map]
  | some q =>
    have hv : ValidOp (P.code q) s := by
      cases hop : P.code q <;> simp only [Valid, ValidOp, hop] at h ⊢ <;> exact h
    simpa only [clock, Nat.add_sub_cancel] using one_step P q s hv out bits

def Safe {K : ℕ} (P : Program K) (S : ℕ) : ℕ → Config P → Prop
  | 0, c => size c.store ≤ S
  | n+1, c => Valid P c ∧ size c.store ≤ S ∧
      ∀ b, Safe P S n (step P c b)

def tree {K : ℕ} (P : Program K) : ℕ → Config P → RandomTree (Config P)
  | 0, c => .leaf c
  | n+1, c => .coin (tree P n (step P c false)) (tree P n (step P c true))

noncomputable def schedule {K : ℕ} (P : Program K) : ℕ → Config P → RandomTree (Config P)
  | 0, c => .leaf c
  | n+1, c => wait (clock P c - 1)
      (.coin (schedule P n (step P c false)) (schedule P n (step P c true)))

theorem schedule_expect {K : ℕ} (P : Program K) (n : ℕ) (c : Config P) (f : Config P → ℚ) :
    (schedule P n c).expect f = (tree P n c).expect f := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [schedule, tree, expect_wait, expect, ih]

theorem schedule_all {K : ℕ} (P : Program K) (n : ℕ) (c : Config P) (Q : Config P → Prop) :
    (schedule P n c).All Q ↔ (tree P n c).All Q := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [schedule, tree, all_wait, All, ih]

theorem schedule_depth {K : ℕ} (P : Program K) (S n : ℕ) (c : Config P)
    (h : Safe P S n c) : (schedule P n c).bitDepth ≤ n * (7*S+4) := by
  induction n generalizing c with
  | zero => simp [schedule, bitDepth]
  | succ n ih =>
    obtain ⟨hv, hs, hn⟩ := h
    have ht := clock_bound P c hv
    have hp := clock_pos P c
    have h₀ := ih _ (hn false)
    have h₁ := ih _ (hn true)
    simp only [schedule, depth_wait, bitDepth]
    rw [Nat.succ_mul]
    omega

theorem consume_step {K : ℕ} (P : Program K) (n : ℕ) (c : Config P)
    (bits : ℕ → Bool) (pos : ℕ) :
    (schedule P (n+1) c).consume bits pos =
      (schedule P n (step P c (bits (pos + (clock P c - 1))))).consume bits (pos + clock P c) := by
  have hp := clock_pos P c
  simp only [schedule, consume_wait, consume]
  cases hb : bits (pos + (clock P c - 1)) <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;> congr 1 <;> omega

theorem consume_simulation {K : ℕ} (P : Program K) (S n : ℕ) (c : Config P)
    (h : Safe P S n c) (bits : ℕ → Bool) (pos : ℕ) :
    let r := (schedule P n c).consume bits pos
    advance (compile P) (fun j => bits (pos+j)) (embed P c) (r.2-pos) = embed P r.1 := by
  induction n generalizing c pos with
  | zero => simp [schedule, consume, advance]
  | succ n ih =>
    obtain ⟨hv, hs, hn⟩ := h
    simp only [consume_step]
    let a := clock P c
    let d := step P c (bits (pos + (a-1)))
    let r := (schedule P n d).consume bits (pos+a)
    have hr : pos+a ≤ r.2 := (consume_path (schedule P n d) bits (pos+a)).1
    have hi := ih d (hn _) (pos+a)
    change advance (compile P) (fun j => bits (pos+j)) (embed P c) (r.2-pos) = _
    rw [show r.2-pos = a+(r.2-(pos+a)) by omega, BinaryData.Take.advance_add]
    rw [clock_simulation P c hv (fun j => bits (pos+j))]
    simpa only [Nat.add_assoc] using hi

theorem embed_halted {K : ℕ} (P : Program K) (c : Config P) (h : c.control = none) :
    (embed P c).control = none := by simp [embed, h, Option.map]

theorem padded_run {K : ℕ} (P : Program K) (S n : ℕ) (c : Config P)
    (h : Safe P S n c) (hh : (tree P n c).All (fun d => d.control = none)) (bits : ℕ → Bool) :
    advance (compile P) bits (embed P c) (n*(7*S+4)) =
      embed P ((schedule P n c).read bits) := by
  let t := schedule P n c
  let r := t.consume bits 0
  have hp : Path t r.1 r.2 := by simpa only [Nat.sub_zero] using (consume_path t bits 0).2
  have hb : r.2 ≤ n*(7*S+4) := hp.depth_le.trans (schedule_depth P S n c h)
  have hd : r.1.control = none := hp.all ((schedule_all P n c _).2 hh)
  have hs : advance (compile P) bits (embed P c) r.2 = embed P r.1 := by
    simpa only [Nat.zero_add, Nat.sub_zero] using consume_simulation P S n c h bits 0
  rw [show n*(7*S+4) = r.2 + (n*(7*S+4)-r.2) by omega, BinaryData.Take.advance_add, hs,
    advance_halted _ _ (embed_halted P r.1 hd)]
  congr 1
  simpa only [Nat.zero_add] using (consume_read t bits 0)

end MeanPayoff.ForestMachine
namespace MeanPayoff.SourceControl

def trialCredit (t : ℕ) : ℕ := 3*t+1
def askCredit (n B : ℕ) : ℕ := trialCredit (globalJ n B)+2
def exceptionCredit (n B : ℕ) : ℕ := askCredit n B+3
def updateCredit (n B : ℕ) : ℕ := 2*askCredit n B+3
def centersCredit (n B t : ℕ) : ℕ := t*(updateCredit n B+3)+1
def orientUnit (n B : ℕ) : ℕ := centersCredit n B (globalS B)+2*exceptionCredit n B+3
def orientCredit (n B w : ℕ) : ℕ := (Nat.clog 2 w+1)*orientUnit n B
def orientTrialsCredit (n B w t : ℕ) : ℕ := t*(orientCredit n B w+3)+1
def orientPlusCredit (n B w : ℕ) : ℕ := orientTrialsCredit n B w (globalJ n B)+2
def tightenUnit (n B : ℕ) : ℕ := 2*askCredit n B+5
def tightenCredit {n B : ℕ} (I : SolveBox n B) : ℕ :=
  (volume I.b I.a / I.delta+1)*tightenUnit n B
def reweightCredit (n B t : ℕ) : ℕ := t*exceptionCredit n B+1

def Result.credit {G : Game} {B : ℕ} (A : Result G B) (v : A.Value) : ℕ :=
  match A with
  | .orientation _ => v.exceptions.length * exceptionCredit G.n B
  | .orientations _ => (v.map Orientation.exceptions).flatten.length * exceptionCredit G.n B
  | .vector _ | .vectors _ | .inner _ => 0

def Job.credit {G : Game} {B : ℕ} {A : Result G B} : Job G B A → ℕ
  | .solve .. => 0
  | .ask .. => askCredit G.n B
  | .trials _ _ t => trialCredit t
  | .update .. => updateCredit G.n B
  | .centers _ _ _ _ t _ => centersCredit G.n B t
  | .orient _ _ I => orientCredit G.n B I.width
  | .orientTrials _ _ I t => orientTrialsCredit G.n B I.width t
  | .orientPlus _ _ I => orientPlusCredit G.n B I.width
  | .tighten _ _ I _ => tightenCredit I
  | .reweight _ _ _ _ Hs => reweightCredit G.n B Hs.length

def Frame.credit {G : Game} {B : ℕ} {A C : Result G B} : Frame G B A C → ℕ
  | .trialsHead _ _ t => trialCredit t+2
  | .vectorCons _ | .median _ | .centerSecond .. => 1
  | .centerFirst .. => askCredit G.n B+2
  | .centersHead _ _ _ _ t _ => centersCredit G.n B t+2
  | .orientLoop _ _ I _ => orientCredit G.n B (2*I.E)+2*exceptionCredit G.n B+2
  | .orientTail .. => 2*exceptionCredit G.n B+1
  | .orientHead _ _ I t => orientTrialsCredit G.n B I.width t+2
  | .orientCons O => O.exceptions.length*exceptionCredit G.n B+1
  | .combine _ => 1
  | .tightenFirst _ _ I _ => (volume I.b I.a / I.delta)*tightenUnit G.n B+askCredit G.n B+4
  | .tightenSecond _ _ I _ => (volume I.b I.a / I.delta)*tightenUnit G.n B+3
  | .floor .. | .ceiling .. => 1
  | .solveTight _ _ I _ => orientPlusCredit G.n B I.width+6
  | .solveOriented .. => 4
  | .reweightHead _ _ _ _ Hs => reweightCredit G.n B Hs.length+2
  | .solveReweighted .. => 2
  | .capHigh .. | .capLow .. | .includeInner _ => 1

def Kont.credit {G : Game} {B : ℕ} {A R : Result G B} : Kont G B A R → ℕ
  | .done => 0
  | .push f k => f.credit+k.credit

def State.credit {G : Game} {B : ℕ} {R : Result G B} : State G B R → ℕ
  | .call j k => j.credit+k.credit
  | .ret (A := A) k v => A.credit v+k.credit

def State.halted {G : Game} {B : ℕ} {R : Result G B} : State G B R → Prop
  | .ret .done _ => True
  | _ => False

def controlAllowance (n B : ℕ) : ℕ :=
  (8*n*globalS B+1)*tightenUnit n B+
    orientPlusCredit n B (B+1)+7

theorem orientCredit_mono {n B v w : ℕ} (h : v ≤ w) :
    orientCredit n B v ≤ orientCredit n B w := by
  exact Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.clog_mono_right 2 h) 1)

theorem orientPlusCredit_mono {n B v w : ℕ} (h : v ≤ w) :
    orientPlusCredit n B v ≤ orientPlusCredit n B w := by
  unfold orientPlusCredit orientTrialsCredit
  gcongr
  exact orientCredit_mono h

theorem orientBase_credit (G : Game) {B : ℕ} (P : Budgets G.n) (I : SolveBox G.n B) :
    (Result.orientation (B := B) P).credit (orientBase G P I) = exceptionCredit G.n B := by
  simp only [orientBase]
  split_ifs <;> simp [Result.credit]

 theorem resume_credit {G : Game} {B : ℕ} {A C R : Result G B}
    (f : Frame G B A C) (v : A.Value) (k : Kont G B C R) :
    (resume f v k).tree.All (fun p => p.1.credit+1 ≤ A.credit v+f.credit+k.credit) := by
  cases f with
  | orientLoop P hR I hB =>
    simp only [resume]
    split_ifs
    · simp only [Counted.pure, RandomTree.All, State.credit, Result.credit,
        List.length_singleton, one_mul, Frame.credit]
      omega
    · simp only [Counted.pure, RandomTree.All, State.credit, Result.credit,
        List.length_singleton, one_mul, Frame.credit]
      omega
    · apply (RandomTree.all_map _ _ _).mpr
      apply (RandomTree.all_map _ _ _).mpr
      apply RandomTree.all_of_forall
      intro j
      simp only [State.credit, Job.credit, Kont.credit, Frame.credit,
        SolveBox.wideCentered, SolveBox.centered, Result.credit]
      omega
  | tightenFirst P hR I hB =>
    simp only [resume]
    split_ifs with h
    · have hd := quotient_drop (I.delta_positive hB) (volume_floor_drop I v h)
      have hm := Nat.mul_le_mul_right (tightenUnit G.n B) hd
      simp only [Counted.pure, RandomTree.All, State.credit, Job.credit,
        Kont.credit, Frame.credit, Result.credit, tightenCredit]
      have he : (I.withFloor v).delta = I.delta := rfl
      rw [he]
      omega
    · simp only [Counted.pure, RandomTree.All, State.credit, Job.credit,
        Kont.credit, Frame.credit, Result.credit]
      omega
  | tightenSecond P hR I hB =>
    simp only [resume]
    split_ifs with h
    · have hd := quotient_drop (I.delta_positive hB) (volume_ceiling_drop I v h)
      have hm := Nat.mul_le_mul_right (tightenUnit G.n B) hd
      simp only [Counted.pure, RandomTree.All, State.credit, Job.credit,
        Kont.credit, Frame.credit, Result.credit, tightenCredit]
      have he : (I.withCeiling v).delta = I.delta := rfl
      rw [he]
      omega
    · simp [Counted.pure, RandomTree.All, State.credit, Frame.credit, Result.credit]
  | solveTight P hR I hB =>
    simp only [resume, Counted.pure, RandomTree.All, State.credit, Job.credit,
      Kont.credit, Frame.credit, Result.credit, v.width_eq]
    omega
  | solveReweighted P hR I hB side =>
    cases side <;> simp [resume, Counted.pure, RandomTree.All, State.credit,
      Job.credit, Kont.credit, Frame.credit, Result.credit]
  | _ =>
    simp [resume, Counted.pure, RandomTree.All, State.credit, Job.credit,
      Kont.credit, Frame.credit, Result.credit, combineOrientations,
      reweightCredit, List.map_cons, List.length_append,
      Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

 theorem step_credit {G : Game} {B : ℕ} {R : Result G B} (s : State G B R)
    (h : ¬s.halted) :
    (step s).tree.All (fun p => p.1.credit+1 ≤ s.credit+controlAllowance G.n B*p.2) := by
  cases s with
  | ret k v =>
    cases k with
    | done => exact (h trivial).elim
    | push f k =>
      apply RandomTree.all_mono _ (resume_credit f v k)
      intro p hp
      simp only [State.credit, Kont.credit] at hp ⊢
      omega
  | call j k =>
    cases j with
    | solve P I =>
      simp only [step, Counted.charge]
      apply (RandomTree.all_map _ _ _).mpr
      split_ifs with hR hB
      · simp [Counted.pure, RandomTree.All, State.credit, Job.credit, Result.credit,
          controlAllowance]
      · simp [Counted.pure, RandomTree.All, State.credit, Job.credit, Result.credit,
          controlAllowance]
      · have hb : 128*globalS B < I.width := by omega
        have ht := Nat.mul_le_mul_right (tightenUnit G.n B)
          (Nat.add_le_add_right (I.tightening_passes hb) 1)
        have ho : orientPlusCredit G.n B I.width ≤ orientPlusCredit G.n B (B+1) :=
          orientPlusCredit_mono (I.bounded.trans (Nat.le_succ B))
        simp only [Counted.pure, RandomTree.All, State.credit, Job.credit, Kont.credit,
          Frame.credit, Result.credit, Nat.add_zero, Nat.mul_one]
        unfold tightenCredit controlAllowance
        omega
    | orient P hR I =>
      simp only [step]
      split_ifs with hB
      · simp only [Counted.pure, RandomTree.All, State.credit, Job.credit,
          orientBase_credit, Nat.mul_zero, Nat.add_zero]
        unfold orientCredit orientUnit
        have hm := Nat.le_mul_of_pos_left (centersCredit G.n B (globalS B)+2*exceptionCredit G.n B+3)
          (by omega : 0 < Nat.clog 2 I.width+1)
        omega
      · have hb : 128*globalS B < I.width := by omega
        have hs := globalS_large B
        have hr := (I.radius_bounds hb).2.2.2
        have hc := clog_double_decrease (by omega : 1 < I.width) (by omega : 2*(2*I.E) ≤ I.width)
        have hm := Nat.mul_le_mul_right (orientUnit G.n B) hc
        simp only [Counted.pure, RandomTree.All, State.credit, Job.credit,
          Kont.credit, Frame.credit, Nat.mul_zero, Nat.add_zero]
        unfold orientCredit
        calc
          _ = (Nat.clog 2 (2*I.E)+1)*orientUnit G.n B+orientUnit G.n B+k.credit := by
            unfold orientUnit
            omega
          _ ≤ Nat.clog 2 I.width*orientUnit G.n B+orientUnit G.n B+k.credit := by omega
          _ = _ := by rw [Nat.add_mul, one_mul]
    | trials P I t =>
      cases t <;> simp [step, Counted.pure, RandomTree.All, State.credit, Job.credit,
        Kont.credit, Frame.credit, Result.credit, trialCredit] ; omega
    | centers P hR I hB t q =>
      cases t <;> simp [step, Counted.pure, RandomTree.All, State.credit, Job.credit,
        Kont.credit, Frame.credit, Result.credit, centersCredit, Nat.add_mul] ; omega
    | orientTrials P hR I t =>
      cases t <;> simp [step, Counted.pure, RandomTree.All, State.credit, Job.credit,
        Kont.credit, Frame.credit, Result.credit, orientTrialsCredit, Nat.add_mul] ; omega
    | reweight P hR I side Hs =>
      cases Hs <;> simp [step, Counted.pure, RandomTree.All, State.credit, Job.credit,
        Kont.credit, Frame.credit, Result.credit, reweightCredit, exceptionCredit, Nat.add_mul] ; omega
    | _ =>
      simp [step, Counted.pure, RandomTree.All, State.credit, Job.credit,
        Kont.credit, Frame.credit, Result.credit, askCredit, updateCredit,
        orientPlusCredit, tightenCredit, tightenUnit, Nat.add_mul] ; omega

end MeanPayoff.SourceControl
end

end OAI
