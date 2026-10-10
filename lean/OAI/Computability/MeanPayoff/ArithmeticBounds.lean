import OAI.Computability.MeanPayoff.StackSimulation

namespace OAI

section
namespace MeanPayoff
namespace RandomTree

def maximum {α : Type} : RandomTree α → (α → ℕ) → ℕ
  | .leaf a, f => f a
  | .coin l r, f => max (maximum l f) (maximum r f)

theorem maximum_le_iff {α : Type} (t : RandomTree α) (f : α → ℕ) (N : ℕ) :
    t.maximum f ≤ N ↔ t.All (fun a => f a ≤ N) := by
  induction t with
  | leaf a => rfl
  | coin l r hl hr => simp only [maximum, max_le_iff, All, hl, hr]

theorem all_le_maximum {α : Type} (t : RandomTree α) (f : α → ℕ) :
    t.All (fun a => f a ≤ t.maximum f) := (maximum_le_iff t f _).mp le_rfl

theorem maximum_add {α : Type} (t : RandomTree α) (f : α → ℕ) (c : ℕ) :
    t.maximum (fun a => c+f a) = c+t.maximum f := by
  induction t with
  | leaf a => rfl
  | coin l r hl hr => simp only [maximum, hl, hr, ← Nat.add_max_add_left]

theorem not_all_false {α : Type} (t : RandomTree α) : ¬t.All (fun _ => False) := by
  induction t with
  | leaf a => exact id
  | coin l r hl hr => exact fun h => hl h.1

end RandomTree
namespace Counted

def maximum {α : Type} (t : Counted α) : ℕ := t.tree.maximum Prod.snd

theorem maximum_le_iff {α : Type} (t : Counted α) (N : ℕ) :
    t.maximum ≤ N ↔ t.Bounded N := RandomTree.maximum_le_iff _ _ _

theorem maximum_bind {α β : Type} (t : Counted α) (f : α → Counted β) :
    t.tree.All (fun p => p.2+(f p.1).maximum ≤ (t.bind f).maximum) := by
  have h := RandomTree.all_le_maximum (t.bind f).tree Prod.snd
  simp only [bind, RandomTree.all_bind, RandomTree.all_map] at h
  apply RandomTree.all_mono _ h
  intro p hp
  have hm := (RandomTree.maximum_le_iff (f p.1).tree (fun q => p.2+q.2) _).mpr hp
  simpa only [RandomTree.maximum_add, maximum, bind] using hm

end Counted
namespace SourceControl

def State.rank {G : Game} {B : ℕ} {R : Result G B} (s : State G B R) : ℕ :=
  s.credit+controlAllowance G.n B*s.denote.maximum

theorem step_rank {G : Game} {B : ℕ} {R : Result G B} (s : State G B R)
    (h : ¬s.halted) : (step s).tree.All (fun p => p.1.rank < s.rank) := by
  have hc := step_credit s h
  have hm := Counted.maximum_bind (step s) State.denote
  rw [step_denote] at hm
  apply RandomTree.all_mono _ (RandomTree.all_and _ hc hm)
  intro p hp
  have hmul := Nat.mul_le_mul_left (controlAllowance G.n B) hp.2
  rw [Nat.mul_add] at hmul
  simp only [State.rank]
  omega

def run {G : Game} {B : ℕ} {R : Result G B} : ℕ → State G B R → Counted (State G B R)
  | 0, s => Counted.pure s
  | n+1, s => (step s).bind (run n)

theorem run_halted {G : Game} {B : ℕ} {R : Result G B} (n : ℕ) (s : State G B R)
    (h : s.halted) : run n s = Counted.pure s := by
  cases s with
  | call j k => exact h.elim
  | ret k v =>
    cases k with
    | push f k => exact h.elim
    | done =>
      induction n with
      | zero => rfl
      | succ n ih => simpa only [run, step, Counted.pure_bind] using ih

theorem run_halts {G : Game} {B : ℕ} {R : Result G B} (n : ℕ) (s : State G B R)
    (hn : s.rank ≤ n) : (run n s).tree.All (fun p => p.1.halted) := by
  induction n generalizing s with
  | zero =>
    change s.halted
    by_contra h
    have hd := step_rank s h
    exact RandomTree.not_all_false (step s).tree
      (RandomTree.all_mono _ hd (fun p hp => by omega))
  | succ n ih =>
    by_cases h : s.halted
    · rw [run_halted _ _ h]
      exact h
    · simp only [run, Counted.bind, RandomTree.all_bind, RandomTree.all_map]
      apply RandomTree.all_mono _ (step_rank s h)
      intro p hp
      exact ih p.1 (by omega)

theorem run_denote {G : Game} {B : ℕ} {R : Result G B} (n : ℕ) (s : State G B R) :
    (run n s).bind State.denote = s.denote := by
  induction n generalizing s with
  | zero => exact Counted.pure_bind _ _
  | succ n ih => simp only [run, Counted.bind_assoc, ih, step_denote]

theorem run_solve_halts (G : Game) {B : ℕ} (P : Budgets G.n) (I : SolveBox G.n B) :
    (run (controlAllowance G.n B*callBound G.n B (parameterRank P.parameter))
      (.call (.solve P I) .done)).tree.All (fun p => p.1.halted) := by
  apply run_halts
  simp only [State.rank, State.credit, Job.credit, Kont.credit, Nat.zero_add,
    State.denote, Job.denote, Kont.denote, Counted.bind_pure]
  exact Nat.mul_le_mul_left _ ((Counted.maximum_le_iff _ _).mpr
    (CountedAlgorithm.bounded_solve G P I))

end SourceControl
end MeanPayoff
namespace MeanPayoff.SourceControl

theorem affine_power {a X d k c : ℕ} (hX : 1 ≤ X) (ha : a ≤ X^d)
    (hk : k+c ≤ X) : k*a+c ≤ X^(d+1) := by
  have hp : 1 ≤ X^d := Nat.one_le_pow _ _ hX
  have hm := Nat.mul_le_mul_left k ha
  have hh := Nat.mul_le_mul_right (X^d) hk
  rw [pow_succ]
  nlinarith only [hp, hm, hh]

theorem controlAllowance_scale {n B X : ℕ} (hX : 32 ≤ X) (hn : n+1 ≤ X)
    (hg : globalG B+1 ≤ X) (hs : globalS B ≤ X) :
    controlAllowance n B ≤ X^39 := by
  have hx : 1 ≤ X := by omega
  have hj := globalJ_scale hX hn hs
  have ha : askCredit n B ≤ X^15 := by
    simpa only [askCredit, trialCredit, Nat.add_assoc] using
      (affine_power hx hj (by omega : 3+3 ≤ X))
  have he : exceptionCredit n B ≤ X^16 := by
    simpa only [one_mul, exceptionCredit] using (affine_power hx ha (by omega : 1+3 ≤ X))
  have hu : updateCredit n B ≤ X^16 := by
    exact affine_power hx ha (by omega : 2+3 ≤ X)
  have hu3 : updateCredit n B+3 ≤ X^17 := by
    simpa only [one_mul] using (affine_power hx hu (by omega : 1+3 ≤ X))
  have hcent0 := Nat.mul_le_mul hs hu3
  have hcent0' : globalS B*(updateCredit n B+3) ≤ X^18 := by
    simpa only [← pow_succ'] using hcent0
  have hcent : centersCredit n B (globalS B) ≤ X^19 := by
    simpa only [centersCredit, one_mul] using (affine_power hx hcent0' (by omega : 1+1 ≤ X))
  have he19 : exceptionCredit n B ≤ X^19 := he.trans (Nat.pow_le_pow_right hx (by norm_num))
  have hunit0 : orientUnit n B ≤ 3*X^19+3 := by unfold orientUnit; omega
  have hunit : orientUnit n B ≤ X^20 := hunit0.trans (affine_power hx le_rfl (by omega : 3+3 ≤ X))
  have hoc : orientCredit n B (B+1) ≤ X^21 := by
    have h := Nat.mul_le_mul (by unfold globalG at hg; omega : Nat.clog 2 (B+1)+1 ≤ X) hunit
    simpa only [orientCredit, ← pow_succ'] using h
  have hoc3 : orientCredit n B (B+1)+3 ≤ X^22 := by
    simpa only [one_mul] using (affine_power hx hoc (by omega : 1+3 ≤ X))
  have hp0 : globalJ n B*(orientCredit n B (B+1)+3) ≤ X^36 := by
    simpa only [← pow_add] using Nat.mul_le_mul hj hoc3
  have hp : orientPlusCredit n B (B+1) ≤ X^37 := by
    simpa only [orientPlusCredit, orientTrialsCredit, Nat.add_assoc, one_mul] using
      (affine_power hx hp0 (by omega : 1+3 ≤ X))
  have htu : tightenUnit n B ≤ X^16 := affine_power hx ha (by omega : 2+5 ≤ X)
  have hns := Nat.mul_le_mul (by omega : n ≤ X) hs
  have hfact : 8*n*globalS B+1 ≤ X^3 := by
    have hsq : 8*n*globalS B+1 ≤ 8*X^2+1 := by nlinarith only [hns]
    exact hsq.trans (affine_power hx le_rfl (by omega : 8+1 ≤ X))
  have ht : (8*n*globalS B+1)*tightenUnit n B ≤ X^19 := by
    simpa only [← pow_add] using Nat.mul_le_mul hfact htu
  have ht37 := ht.trans (Nat.pow_le_pow_right hx (by norm_num : 19 ≤ 37))
  have hall : controlAllowance n B ≤ 2*X^37+7 := by unfold controlAllowance; omega
  exact (hall.trans (affine_power hx le_rfl (by omega : 2+7 ≤ X))).trans
    (Nat.pow_le_pow_right hx (by norm_num : 38 ≤ 39))

noncomputable def rootControlBound (G : Game) : ℕ :=
  controlAllowance G.n (topWidth G).toNat * rootInvocationBound G

theorem rootControlBound_nat (G : Game) :
    rootControlBound G ≤ 2^(25000*(Nat.clog 2 ((input G).length+2))^2) := by
  let h := Nat.clog 2 ((input G).length+2)
  have hh : 1 ≤ h := by
    apply (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).mpr
    simp only [pow_zero]
    omega
  have hk := controlAllowance_scale (inputScale_large G) (inputScale_n G)
    (inputScale_g G) (inputScale_s G)
  have hx : inputScale G ≤ 2^(24+h) := by
    have hp := Nat.le_pow_clog (by norm_num : 1 < 2) ((input G).length+2)
    have hm := Nat.mul_le_mul_left (2^24) hp
    simpa only [inputScale, pow_add] using hm
  have hk' : controlAllowance G.n (topWidth G).toNat ≤ 2^((24+h)*39) :=
    hk.trans (by simpa only [← pow_mul] using Nat.pow_le_pow_left hx 39)
  have hi := rootInvocationBound_nat G
  have ht := Nat.mul_le_mul hk' hi
  rw [← pow_add] at ht
  apply ht.trans
  apply Nat.pow_le_pow_right (by norm_num)
  change (24+h)*39+24000*h^2 ≤ 25000*h^2
  nlinarith only [hh]

theorem root_operational_halts (G : Game) :
    (run (rootControlBound G) (.call (.solve (rootBudgets G) (rootBox G)) .done)).tree.All
      (fun p => p.1.halted) := run_solve_halts G _ _

end MeanPayoff.SourceControl
namespace MeanPayoff
namespace WorkStack.RegisterCompile

inductive Label (s : ℕ) where
  | get0 (q : Fin s)
  | get1 (q : Fin s) (a : Option Bool) (coin : Bool)
  | get2 (q : Fin s) (a b : Option Bool) (coin : Bool)
  | put (q : Fin s) (top : Fin 3 → Option Bool) (coin : Bool) (k : Fin 3)
  deriving DecidableEq, Fintype

noncomputable def equiv (P : Program) : Label P.states ≃ Fin (Fintype.card (Label P.states)) :=
  Fintype.equivFin _
noncomputable def enc (P : Program) (q : Label P.states) := equiv P q
@[simp] theorem decode (P : Program) (q : Label P.states) : (equiv P).symm (enc P q) = q :=
  (equiv P).symm_apply_apply q

noncomputable def program (P : Program) : RegisterBits.Program 3 where
  states := Fintype.card (Label P.states)
  start := enc P (.get0 P.start)
  read q := match (equiv P).symm q with
    | .get0 _ => 0
    | .get1 _ _ _ => 1
    | .get2 _ _ _ _ => 2
    | .put _ _ _ k => k
  transition q top coin := match (equiv P).symm q with
    | .get0 q => some ⟨enc P (.get1 q top coin), .keep, none⟩
    | .get1 q a c => some ⟨enc P (.get2 q a top c), .keep, none⟩
    | .get2 q a b c => some ⟨enc P (.put q ![a,b,top] c 0), .keep, none⟩
    | .put q ts c k => match P.transition q ts c with
      | none => none
      | some a => some ⟨enc P (if h : k.val = 2 then .get0 a.next else
          .put q ts c ⟨k.val+1, by have := k.isLt; omega⟩), a.work k, none⟩

noncomputable def lift (P : Program) (out : List Bool) (c : Config P) :
    RegisterBits.Config (program P) :=
  ⟨c.control.map (fun q => enc P (.get0 q)), c.stack, out⟩

noncomputable def state (P : Program) (q : Label P.states) (xs : Fin 3 → List Bool)
    (out : List Bool) : RegisterBits.Config (program P) := ⟨some (enc P q), xs, out⟩

@[simp] theorem read0 (P : Program) (q : Fin P.states) (xs : Fin 3 → List Bool)
    (out : List Bool) (b : Bool) :
    RegisterBits.step (program P) (state P (.get0 q) xs out) b =
      state P (.get1 q (xs 0).head? b) xs out := by
  simp [RegisterBits.step, program, state, BinaryStack.applyOp]

@[simp] theorem read1 (P : Program) (q : Fin P.states) (a : Option Bool) (c b : Bool)
    (xs : Fin 3 → List Bool) (out : List Bool) :
    RegisterBits.step (program P) (state P (.get1 q a c) xs out) b =
      state P (.get2 q a (xs 1).head? c) xs out := by
  simp [RegisterBits.step, program, state, BinaryStack.applyOp]

@[simp] theorem read2 (P : Program) (q : Fin P.states) (a d : Option Bool) (c b : Bool)
    (xs : Fin 3 → List Bool) (out : List Bool) :
    RegisterBits.step (program P) (state P (.get2 q a d c) xs out) b =
      state P (.put q ![a,d,(xs 2).head?] c 0) xs out := by
  simp [RegisterBits.step, program, state, BinaryStack.applyOp]

@[simp] theorem put_step (P : Program) (q : Fin P.states) (ts : Fin 3 → Option Bool)
    (c b : Bool) (k : Fin 3) (xs : Fin 3 → List Bool) (out : List Bool)
    (a : Act P.states) (ha : P.transition q ts c = some a) :
    RegisterBits.step (program P) (state P (.put q ts c k) xs out) b =
      state P (if h : k.val = 2 then .get0 a.next else
        .put q ts c ⟨k.val+1, by have := k.isLt; omega⟩)
        (Function.update xs k (BinaryStack.applyOp (a.work k) (xs k))) out := by
  simp [RegisterBits.step, program, state, ha]

@[simp] theorem put_stop (P : Program) (q : Fin P.states) (ts : Fin 3 → Option Bool)
    (c b : Bool) (k : Fin 3) (xs : Fin 3 → List Bool) (out : List Bool)
    (ha : P.transition q ts c = none) :
    RegisterBits.step (program P) (state P (.put q ts c k) xs out) b =
      ⟨none, xs, out⟩ := by
  simp [RegisterBits.step, program, state, ha]

theorem six_steps (P : Program) (out : List Bool) (c : Config P) (bits : ℕ → Bool) :
    RegisterBits.advance (program P) bits (lift P out c) 6 =
      lift P out (step P c (bits 0)) := by
  rcases c with ⟨q,xs⟩
  cases q with
  | none => rfl
  | some q =>
    have ht : ![(xs 0).head?, (xs 1).head?, (xs 2).head?] =
        (fun i => (xs i).head?) := by funext i; fin_cases i <;> rfl
    change RegisterBits.advance _ bits (state P (.get0 q) xs out) 6 = _
    simp only [RegisterBits.advance, read0, read1, read2, ht]
    cases ha : P.transition q (fun i => (xs i).head?) (bits 0) with
    | none =>
      rw [put_stop (ha := ha)]
      simp [RegisterBits.step, step, ha, lift]
      rfl
    | some a =>
      simp only [put_step (ha := ha), Fin.val_zero, Nat.reduceAdd, Nat.reduceEqDiff, dite_false, dite_true]
      apply BinaryData.Take.config_ext
      · simp [step, ha, lift, state]; rfl
      · funext i; fin_cases i <;> simp [step, ha, lift, state]
      · rfl

theorem advance_six (P : Program) (out : List Bool) (c : Config P) (bits : ℕ → Bool)
    (n : ℕ) :
    RegisterBits.advance (program P) bits (lift P out c) (6*n) =
      lift P out (advance P (fun i => bits (6*i)) c n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 6*(n+1) = 6*n+6 by omega, BinaryData.Take.advance_add, ih, six_steps]
    rfl

end WorkStack.RegisterCompile
end MeanPayoff
end

end OAI
