import OAI.Computability.WeisfeilerLeman.Circuits

namespace OAI

universe uJ

namespace WLTime

structure OneTape where
  states : ℕ
  symbols : ℕ
  states_ge : 3  ≤  states
  symbols_ge : 3  ≤  symbols
  transition : Fin states → Fin symbols → Fin states × Fin symbols × Move

namespace OneTape
variable (M : OneTape)
open scoped Classical

abbrev Cell := Fin M.symbols × Option (Fin M.states)

def action (q : Fin M.states) (s : Fin M.symbols) : Fin M.states × Fin M.symbols × Move :=
  if q.val=1 ∨ q.val=2 then (q,s,.stay) else M.transition q s

structure Config (J : Type uJ) where
  state : Fin M.states
  head : J
  tape : J → Fin M.symbols

def moveAt {J : Type uJ} (shift : Equiv.Perm J) : Move → J → J
  | .left => shift.symm
  | .stay => id
  | .right => shift

open scoped Classical in
noncomputable def step {J : Type uJ} (shift : Equiv.Perm J) (C : M.Config J) : M.Config J :=
  let a := M.action C.state (C.tape C.head)
  { state := a.1
    head := moveAt shift a.2.2 C.head
    tape := Function.update C.tape C.head a.2.1 }

open scoped Classical in
noncomputable def snapshot {J : Type uJ} (C : M.Config J) (j : J) : M.Cell :=
  (C.tape j,if j=C.head then some C.state else none)

def written (c : M.Cell) : Fin M.symbols := match c.2 with
  | none => c.1
  | some q => (M.action q c.1).2.1

def arrival (d : Move) (c : M.Cell) : Option (Fin M.states) := match c.2 with
  | none => none
  | some q => if (M.action q c.1).2.2=d then some (M.action q c.1).1 else none

def localRule (l c r : M.Cell) : M.Cell :=
  (M.written c,(M.arrival .stay c).or (M.arrival .right l) |>.or (M.arrival .left r))

variable {J : Type uJ}

theorem written_snapshot (C : M.Config J) (j : J) :
    M.written (M.snapshot C j) =
      if j=C.head then (M.action C.state (C.tape C.head)).2.1 else C.tape j := by
  classical
  by_cases hj : j=C.head <;> simp [written,snapshot,hj]

theorem arrival_snapshot (C : M.Config J) (j : J) (d : Move) :
    M.arrival d (M.snapshot C j) =
      if j=C.head ∧ (M.action C.state (C.tape C.head)).2.2=d then
        some (M.action C.state (C.tape C.head)).1 else none := by
  classical
  by_cases hj : j=C.head <;> simp [arrival,snapshot,hj]

theorem moveAt_eq_iff (shift : Equiv.Perm J) (d : Move) (h j : J) :
    j=moveAt shift d h ↔ (j=h ∧ d=.stay) ∨
      (shift.symm j=h ∧ d=.right) ∨ (shift j=h ∧ d=.left) := by
  cases d with
  | left => simp [moveAt,Equiv.eq_symm_apply]
  | stay => simp [moveAt]
  | right => simp [moveAt,Equiv.symm_apply_eq]

theorem snapshot_step (shift : Equiv.Perm J) (C : M.Config J) (j : J) :
    M.snapshot (M.step shift C) j =
      M.localRule (M.snapshot C (shift.symm j)) (M.snapshot C j) (M.snapshot C (shift j)) := by
  classical
  apply Prod.ext
  · change (Function.update C.tape C.head (M.action C.state (C.tape C.head)).2.1) j =
      M.written (M.snapshot C j)
    rw [M.written_snapshot]
    exact Function.update_apply _ _ _ _
  · change (if j=moveAt shift (M.action C.state (C.tape C.head)).2.2 C.head then
        some (M.action C.state (C.tape C.head)).1 else none) =
      ((M.arrival .stay (M.snapshot C j)).or (M.arrival .right (M.snapshot C (shift.symm j)))).or
        (M.arrival .left (M.snapshot C (shift j)))
    simp only [M.arrival_snapshot,moveAt_eq_iff]
    by_cases h0 : j=C.head ∧ (M.action C.state (C.tape C.head)).2.2=.stay <;>
      by_cases h1 : shift.symm j=C.head ∧ (M.action C.state (C.tape C.head)).2.2=.right <;>
      by_cases h2 : shift j=C.head ∧ (M.action C.state (C.tape C.head)).2.2=.left <;>
      simp [h0,h1,h2]

noncomputable def run {J : Type uJ} (shift : Equiv.Perm J) (C : M.Config J) (t : ℕ) : M.Config J :=
  (M.step shift)^[t] C

theorem run_snapshot (shift : Equiv.Perm J) (C : M.Config J) (t : ℕ) :
    M.snapshot (M.run shift C t) =
      CircuitEncoding.Tableau.run M.localRule shift (M.snapshot C) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext j
    rw [CircuitEncoding.Tableau.run_succ]
    change M.snapshot ((M.step shift)^[t+1] C) j = _
    rw [Function.iterate_succ_apply']
    change M.snapshot (M.step shift (M.run shift C t)) j = _
    rw [M.snapshot_step,ih]

def toTM : TM where
  tapes := 1
  states := M.states
  symbols := M.symbols
  tapes_pos := by decide
  states_ge := M.states_ge
  symbols_ge := M.symbols_ge
  transition q a := let b := M.transition q (a 0)
    (b.1,fun _ => b.2.1,fun _ => b.2.2)

def embed (C : M.Config ℤ) : M.toTM.Config where
  state := C.state
  head := fun _ => C.head
  tape := fun _ => C.tape

def lineShift : Equiv.Perm ℤ := Equiv.addRight 1

theorem moveAt_line (d : Move) (h : ℤ) : moveAt lineShift d h = h+d.displacement := by
  cases d <;> simp [moveAt,lineShift,Move.displacement ]

theorem embed_step (C : M.Config ℤ) : M.embed (M.step lineShift C) = M.toTM.step (M.embed C) := by
  classical
  by_cases hh : C.state.val=1 ∨ C.state.val=2
  · have hc : M.step lineShift C=C := by
      cases C
      simp_all [step,action,moveAt,Function.update_eq_self]
    rw [hc]
    simp [TM.step,TM.halted,embed,hh]
  · simp only [TM.step,TM.halted,embed,hh,ite_false]
    simp only [step,action,hh,ite_false,toTM,moveAt_line]
    congr
    funext a z
    simp only [Function.update_apply]
    split <;> rename_i hz <;> simp only [hz,ite_true,ite_false]

def initial (w : List Bool) : M.Config ℤ where
  state := ⟨0,by have := M.states_ge; omega⟩
  head := 0
  tape z := if 0 ≤ z ∧ z.toNat< w.length then
    M.toTM.symbol (w.getD z.toNat false) else ⟨0,by have := M.symbols_ge; omega⟩

@[simp] theorem embed_initial (w : List Bool) : M.embed (M.initial w)=M.toTM.initial w := by
  unfold embed initial TM.initial
  congr 1
  funext a z
  have ha : a.val=0 := Fin.eq_zero a ▸ rfl
  simp only [ha,true_and]
  split <;> rename_i hz <;> simp [hz] <;> rfl

theorem embed_run (w : List Bool) (t : ℕ) :
    M.embed (M.run lineShift (M.initial w) t)=M.toTM.run w t := by
  induction t with
  | zero => exact M.embed_initial w
  | succ t ih =>
    change M.embed ((M.step lineShift)^[t+1] (M.initial w)) = M.toTM.step^[t+1] (M.toTM.initial w)
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    rw [M.embed_step]
    exact congrArg M.toTM.step ih

theorem step_halted {J : Type uJ} (shift : Equiv.Perm J) (C : M.Config J)
    (hh : C.state.val=1 ∨ C.state.val=2) : M.step shift C=C := by
  cases C
  simp_all [step,action,moveAt,Function.update_eq_self]

theorem run_halted {J : Type uJ} (shift : Equiv.Perm J) (C : M.Config J)
    (hh : C.state.val=1 ∨ C.state.val=2) (t : ℕ) : M.run shift C t=C := by
  unfold run
  exact Function.iterate_fixed (M.step_halted shift C hh) t

theorem line_head_step (C : M.Config ℤ) :
    C.head-1  ≤  (M.step lineShift C).head ∧ (M.step lineShift C).head  ≤  C.head+1 := by
  change C.head-1  ≤  moveAt lineShift (M.action C.state (C.tape C.head)).2.2 C.head ∧
    moveAt lineShift (M.action C.state (C.tape C.head)).2.2 C.head  ≤  C.head+1
  rw [moveAt_line]
  cases (M.action C.state (C.tape C.head)).2.2 <;> simp [Move.displacement]
  omega

theorem line_head_run (w : List Bool) (t : ℕ) :
    -(t:ℤ)  ≤  (M.run lineShift (M.initial w) t).head ∧
      (M.run lineShift (M.initial w) t).head  ≤  (t:ℤ) := by
  induction t with
  | zero => simp [run,initial]
  | succ t ih =>
    have hs := M.line_head_step (M.run lineShift (M.initial w) t)
    change -(↑(t+1):ℤ)  ≤  ((M.step lineShift)^[t+1] (M.initial w)).head ∧
      ((M.step lineShift)^[t+1] (M.initial w)).head  ≤  (↑(t+1):ℤ)
    rw [Function.iterate_succ_apply']
    change -(↑(t+1):ℤ)  ≤  (M.step lineShift (M.run lineShift (M.initial w) t)).head ∧
      (M.step lineShift (M.run lineShift (M.initial w) t)).head  ≤  (↑(t+1):ℤ)
    push_cast
    omega

def Agrees {J : Type uJ} (π : ℤ → J) (I : Set ℤ) (C : M.Config ℤ) (D : M.Config J) : Prop :=
  D.state=C.state ∧ D.head=π C.head ∧ ∀ z∈I,D.tape (π z)=C.tape z

theorem agrees_step {J : Type uJ} (shift : Equiv.Perm J) (π : ℤ → J) (I : Set ℤ)
    (hπ : ∀ z,π (z+1)=shift (π z)) (hinj : Set.InjOn π I)
    (C : M.Config ℤ) (D : M.Config J) (ha : M.Agrees π I C D) (hh : C.head∈I) :
    M.Agrees π I (M.step lineShift C) (M.step shift D) := by
  classical
  obtain ⟨hs,hd,ht⟩ := ha
  have scanned : D.tape D.head=C.tape C.head := by rw [hd]; exact ht _ hh
  have moved (d : Move) : moveAt shift d (π C.head)=π (moveAt lineShift d C.head) := by
    rw [moveAt_line]
    cases d with
    | stay => simp [moveAt,Move.displacement]
    | right => exact (hπ C.head).symm
    | left =>
      change shift.symm (π C.head)=π (C.head+(-1))
      apply shift.injective
      rw [shift.apply_symm_apply,← hπ]
      congr 1
      omega
  refine ⟨?_,?_,?_⟩
  · simp only [step,hs,scanned]
  · simp only [step,hs,hd,ht _ hh,moved]
  · intro z hz
    simp only [step]
    rw [hs,scanned,hd]
    have he : π z=π C.head ↔ z=C.head := ⟨hinj hz hh,congrArg π⟩
    simp only [Function.update_apply,he]
    split <;> first | rfl | exact ht z hz

theorem agrees_run {J : Type uJ} (shift : Equiv.Perm J) (π : ℤ → J) (I : Set ℤ)
    (hπ : ∀ z,π (z+1)=shift (π z)) (hinj : Set.InjOn π I)
    (w : List Bool) (D : M.Config J) (ha : M.Agrees π I (M.initial w) D)
    (T : ℕ) (hI : ∀ z : ℤ, -(T:ℤ) ≤ z → z ≤ T → z∈I) :
    ∀ t ≤ T, M.Agrees π I (M.run lineShift (M.initial w) t) (M.run shift D t) := by
  intro t
  induction t with
  | zero => intro _; exact ha
  | succ t ih =>
    intro ht
    have hl := M.line_head_run w t
    have hi : (M.run lineShift (M.initial w) t).head∈I :=
      hI _ (by omega) (by omega)
    have hc := M.agrees_step shift π I hπ hinj _ _ (ih (by omega)) hi
    simpa only [run,Function.iterate_succ_apply'] using hc

theorem run_frozen_after {J : Type uJ} (shift : Equiv.Perm J) (C : M.Config J)
    (t : ℕ) (hh : (M.run shift C t).state.val=1 ∨ (M.run shift C t).state.val=2)
    (s : ℕ) (hts : t ≤ s) : M.run shift C s=M.run shift C t := by
  obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le hts
  change (M.step shift)^[t+u] C = _
  rw [Nat.add_comm,Function.iterate_add_apply]
  exact M.run_halted shift (M.run shift C t) hh u

theorem accepts_iff_state (w : List Bool) (T : ℕ)
    (hh : (M.run lineShift (M.initial w) T).state.val=1 ∨
      (M.run lineShift (M.initial w) T).state.val=2) :
    M.toTM.accepts w ↔ (M.run lineShift (M.initial w) T).state.val=1 := by
  constructor
  · rintro ⟨s,hs⟩
    have hs' : (M.run lineShift (M.initial w) s).state.val=1 := by
      have he := congrArg (fun C : M.toTM.Config => C.state.val) (M.embed_run w s)
      exact he.trans hs
    rcases le_total s T with hst | hts
    · rw [M.run_frozen_after lineShift (M.initial w) s (Or.inl hs') T hst]
      exact hs'
    · rw [M.run_frozen_after lineShift (M.initial w) T hh s hts] at hs'
      exact hs'
  · intro hs
    refine ⟨T,?_⟩
    have he := congrArg (fun C : M.toTM.Config => C.state.val) (M.embed_run w T)
    exact he.symm.trans hs

def protectedInterval (m T : ℕ) : Set ℤ := Set.Icc (-(T:ℤ)-1) ((m:ℤ)+T)

theorem protectedInterval_injective (m T L : ℕ) (hL : 2*T+m+2< L) :
    Set.InjOn (fun z : ℤ => (z : ZMod L)) (protectedInterval m T) := by
  intro x hx y hy he
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub x y L).mp he
  have hL' : (2*(T:ℤ)+m+2)< L := by exact_mod_cast hL
  change -(T:ℤ)-1 ≤ x ∧ x ≤ (m:ℤ)+T at hx
  change -(T:ℤ)-1 ≤ y ∧ y ≤ (m:ℤ)+T at hy
  rcases le_total x y with hxy | hyx
  · have hz : y-x=0 := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega) (by omega) hd
    omega
  · have hd' : (L:ℤ)∣x-y := by simpa only [neg_sub] using (dvd_neg.mpr hd)
    have hz : x-y=0 := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega) (by omega) hd'
    omega

def ringShift (L : ℕ) : Equiv.Perm (ZMod L) := Equiv.addRight 1

noncomputable def ringInitial (L : ℕ) (w : List Bool) : M.Config (ZMod L) where
  state := ⟨0,by have := M.states_ge; omega⟩
  head := 0
  tape j := if j.val< w.length then M.toTM.symbol (w.getD j.val false)
    else ⟨0,by have := M.symbols_ge; omega⟩

theorem ring_initial_agrees (w : List Bool) (T L : ℕ) (hL : 2*T+w.length+2< L) :
    M.Agrees (fun z : ℤ => (z : ZMod L)) (protectedInterval w.length T)
      (M.initial w) (M.ringInitial L w) := by
  classical
  have hp : 0< L := by omega
  let : NeZero L := ⟨Nat.ne_of_gt hp⟩
  refine ⟨rfl,by simp [ringInitial,initial],?_⟩
  intro z hz
  have hinj := protectedInterval_injective w.length T L hL
  have input_mem (i : ℕ) (hi : i< w.length) : (i:ℤ)∈protectedInterval w.length T := by
    change -(T:ℤ)-1 ≤ i ∧ (i:ℤ) ≤ (w.length:ℤ)+T
    constructor <;> omega
  have hi : (z : ZMod L).val< w.length ↔ 0 ≤ z ∧ z.toNat< w.length := by
    constructor
    · intro h
      have he : ((z : ZMod L).val : ℤ)=z := hinj (input_mem _ h) hz (by simp)
      rw [← he]
      simp only [Int.natCast_nonneg,Int.toNat_natCast,true_and]
      exact h
    · rintro ⟨hz0,hzlen⟩
      have he : (((z.toNat:ℕ):ℤ):ZMod L)=(z:ZMod L) := by rw [Int.toNat_of_nonneg hz0]
      have hsmall : z.toNat< L := by omega
      rw [← he]
      simpa only [Int.cast_natCast,ZMod.val_natCast,Nat.mod_eq_of_lt hsmall] using hzlen
  have hv (h : (z : ZMod L).val< w.length) : (z : ZMod L).val=z.toNat := by
    have he : ((z : ZMod L).val : ℤ)=z := hinj (input_mem _ h) hz (by simp)
    simpa only [Int.toNat_natCast] using congrArg Int.toNat he
  simp only [ringInitial,initial]
  by_cases hr : (z : ZMod L).val< w.length
  · simp [hi.mp hr,hv hr]
    rfl
  · simp [hr,show ¬(0 ≤ z ∧ z.toNat< w.length) from fun h => hr (hi.mpr h)]

theorem ring_run_agrees (w : List Bool) (T L : ℕ) (hL : 2*T+w.length+2< L) :
    ∀ t ≤ T,M.Agrees (fun z : ℤ => (z : ZMod L)) (protectedInterval w.length T)
      (M.run lineShift (M.initial w) t) (M.run (ringShift L) (M.ringInitial L w) t) := by
  apply M.agrees_run
  · intro z
    change ((z+1:ℤ):ZMod L)=(z:ZMod L)+1
    push_cast
    rfl
  · exact protectedInterval_injective w.length T L hL
  · exact M.ring_initial_agrees w T L hL
  · intro z hz0 hz1
    change -(T:ℤ)-1 ≤ z ∧ z ≤ (w.length:ℤ)+T
    constructor <;> omega

def letterAccepting (c : M.Cell) : Prop := ∃ q,c.2=some q ∧ q.val=1

theorem accepting_snapshot {J : Type uJ} (C : M.Config J) :
    (∃ j,M.letterAccepting (M.snapshot C j)) ↔ C.state.val=1 := by
  classical
  constructor
  · rintro ⟨j,q,hq,hv⟩
    by_cases hj : j=C.head
    · simp only [snapshot,hj,ite_true,Option.some.injEq] at hq
      exact hq ▸ hv
    · simp [snapshot,hj] at hq
  · intro hv
    exact ⟨C.head,C.state,by simp [snapshot],hv⟩

theorem ring_accepts_iff (w : List Bool) (T L S : ℕ)
    (hL : 2*T+w.length+2< L) (hTS : T ≤ S)
    (hh : (M.run lineShift (M.initial w) T).state.val=1 ∨
      (M.run lineShift (M.initial w) T).state.val=2) :
    (∃ j,M.letterAccepting (CircuitEncoding.Tableau.run M.localRule (ringShift L)
      (M.snapshot (M.ringInitial L w)) S j)) ↔ M.toTM.accepts w := by
  rw [← M.run_snapshot,M.accepting_snapshot,M.accepts_iff_state w T hh]
  have hA := M.ring_run_agrees w T L hL T le_rfl
  have hR : (M.run (ringShift L) (M.ringInitial L w) T).state.val=1 ∨
      (M.run (ringShift L) (M.ringInitial L w) T).state.val=2 := by rw [hA.1]; exact hh
  rw [M.run_frozen_after (ringShift L) (M.ringInitial L w) T hR S hTS,hA.1]

end OneTape
end WLTime

namespace WLTime.TM
variable (M : TM)

theorem run_add (w : List Bool) (a b : ℕ) :
    M.run w (a+b)=M.step^[a] (M.run w b) :=
  Function.iterate_add_apply _ _ _ _

theorem run_succ (w : List Bool) (t : ℕ) : M.run w (t+1)=M.step (M.run w t) :=
  Function.iterate_succ_apply' _ _ _

theorem step_frozen (C : M.Config) (h : M.halted C) : M.step C=C := by
  rw [step,ite_eq_left h]

theorem run_frozen (w : List Bool) {t u : ℕ} (hh : M.halted (M.run w t))
    (hu : t ≤ u) : M.run w u=M.run w t := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_add_of_le hu
  rw [Nat.add_comm,M.run_add]
  exact Function.iterate_fixed (M.step_frozen _ hh) a

theorem time_halted (w : List Bool) (h : M.halts w) : M.halted (M.run w (M.time w)) := by
  simp only [time,dite_eq_left h]
  exact Nat.find_spec h

theorem time_le_of_halted (w : List Bool) {t : ℕ} (h : M.halted (M.run w t)) : M.time w ≤ t := by
  have hh : M.halts w := ⟨t,h⟩
  simp only [time,dite_eq_left hh]
  exact Nat.find_min' hh h

theorem accepts_iff_at_halt (w : List Bool) {t : ℕ} (h : M.halted (M.run w t)) :
    M.accepts w ↔ (M.run w t).state.val=1 := by
  constructor
  · rintro ⟨s,hs⟩
    have hx := M.run_frozen w h (Nat.le_max_right s t)
    have hy := M.run_frozen w (Or.inl hs) (Nat.le_max_left s t)
    rw [hx] at hy
    exact congrArg (fun C : M.Config => C.state.val) hy |>.trans hs
  · intro ht; exact ⟨t,ht⟩

end WLTime.TM

end OAI
