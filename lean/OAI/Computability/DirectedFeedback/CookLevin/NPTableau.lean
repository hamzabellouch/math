import Mathlib
import OAI.Computability.DirectedFeedback.Games.DegreeCover

namespace OAI

section

namespace DirectedFeedback.CookLevin
open Turing
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

abbrev Words (Γ : K → Type) := ∀ k, ℕ → Option (Γ k)

def wordPush {α : Type} (a : α) (w : ℕ → Option α) : ℕ → Option α
  | 0 => some a
  | n+1 => w n

def wordPop {α : Type} (w : ℕ → Option α) : ℕ → Option α := fun n => w (n+1)

def wordsOfLists (S : ∀ k, List (Γ k)) : Words Γ := fun k n => (S k)[n]?

@[simp] theorem wordsOfLists_update (S : ∀ k, List (Γ k)) (k : K) (l : List (Γ k)) :
    wordsOfLists (Function.update S k l) =
      Function.update (wordsOfLists S) k (fun n => l[n]?) := by
  funext j n
  by_cases hj : j = k
  · subst j
    simp [wordsOfLists]
  · simp [wordsOfLists, hj]

@[simp] theorem wordsOfLists_push (S : ∀ k, List (Γ k)) (k : K) (a : Γ k) :
    wordsOfLists (Function.update S k (a :: S k)) =
      Function.update (wordsOfLists S) k (wordPush a (wordsOfLists S k)) := by
  rw [wordsOfLists_update]
  congr 1
  funext n
  cases n <;> rfl

@[simp] theorem wordsOfLists_pop (S : ∀ k, List (Γ k)) (k : K) :
    wordsOfLists (Function.update S k (S k).tail) =
      Function.update (wordsOfLists S) k (wordPop (wordsOfLists S k)) := by
  rw [wordsOfLists_update]
  congr 1
  funext n
  simp [wordPop, wordsOfLists]

structure WordCfg (Γ : K → Type) (Λ σ : Type) where
  label : Option Λ
  var : σ
  stk : Words Γ

def WordCfg.ofCfg (c : TM2.Cfg Γ Λ σ) : WordCfg Γ Λ σ :=
  ⟨c.l,c.var,wordsOfLists c.stk⟩

def wordStepAux : TM2.Stmt Γ Λ σ → σ → Words Γ → WordCfg Γ Λ σ
  | .push k f q, v, S => wordStepAux q v (Function.update S k (wordPush (f v) (S k)))
  | .peek k f q, v, S => wordStepAux q (f v (S k 0)) S
  | .pop k f q, v, S => wordStepAux q (f v (S k 0)) (Function.update S k (wordPop (S k)))
  | .load f q, v, S => wordStepAux q (f v) S
  | .branch f q r, v, S => if f v then wordStepAux q v S else wordStepAux r v S
  | .goto f, v, S => ⟨some (f v),v,S⟩
  | .halt, v, S => ⟨none,v,S⟩

theorem wordStepAux_ofLists (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    wordStepAux q v (wordsOfLists S) = WordCfg.ofCfg (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih => simp only [wordStepAux, TM2.stepAux, WordCfg.ofCfg]; rw [← wordsOfLists_push]; exact ih _ _
  | peek k f q ih => simpa only [wordStepAux, TM2.stepAux, wordsOfLists, ← List.head?_eq_getElem?] using ih (f v (S k).head?) S
  | pop k f q ih =>
      simp only [wordStepAux, TM2.stepAux, WordCfg.ofCfg]
      rw [← wordsOfLists_pop]
      simpa only [wordsOfLists, ← List.head?_eq_getElem?, WordCfg.ofCfg] using ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load f q ih => exact ih _ _
  | branch f q r iq ir => cases h : f v <;> simp [wordStepAux, TM2.stepAux, h, iq, ir]
  | goto f => rfl
  | halt => rfl

def radius : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => radius q + 1
  | .peek _ _ q => radius q + 1
  | .pop _ _ q => radius q + 1
  | .load _ q => radius q
  | .branch _ q r => max (radius q) (radius r)
  | .goto _ => 0
  | .halt => 0

def InCone (r j i : ℕ) : Prop := i < r ∨ (i ≤ j+r ∧ j ≤ i+r)

def AgreeCone (r j : ℕ) (S R : Words Γ) : Prop :=
  ∀ k i, InCone r j i → S k i = R k i

omit [DecidableEq K] in
theorem agreeCone_mono {r s j : ℕ} (hrs : r ≤ s) {S R : Words Γ}
    (h : AgreeCone s j S R) : AgreeCone r j S R := by
  intro k i hi
  apply h
  rcases hi with hi | ⟨hi,hj⟩
  · exact Or.inl (lt_of_lt_of_le hi hrs)
  · exact Or.inr ⟨by omega, by omega⟩

omit [DecidableEq K] in
theorem agreeCone_head {r j : ℕ} {S R : Words Γ}
    (h : AgreeCone (r+1) j S R) (k : K) : S k 0 = R k 0 :=
  h k 0 (Or.inl (Nat.succ_pos _))

theorem agreeCone_push {r j : ℕ} {S R : Words Γ}
    (h : AgreeCone (r+1) j S R) (k : K) (a : Γ k) :
    AgreeCone r j (Function.update S k (wordPush a (S k)))
      (Function.update R k (wordPush a (R k))) := by
  intro l i hi
  by_cases hl : l = k
  · subst l
    simp only [Function.update_self]
    cases i with
    | zero => rfl
    | succ i =>
      apply h
      rcases hi with hi | ⟨hi,hj⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, by omega⟩
  · simpa only [Function.update_of_ne hl] using agreeCone_mono (Nat.le_succ r) h l i hi

theorem agreeCone_pop {r j : ℕ} {S R : Words Γ}
    (h : AgreeCone (r+1) j S R) (k : K) :
    AgreeCone r j (Function.update S k (wordPop (S k)))
      (Function.update R k (wordPop (R k))) := by
  intro l i hi
  by_cases hl : l = k
  · subst l
    simp only [Function.update_self, wordPop]
    apply h
    rcases hi with hi | ⟨hi,hj⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, by omega⟩
  · simpa only [Function.update_of_ne hl] using agreeCone_mono (Nat.le_succ r) h l i hi

theorem wordStepAux_local (q : TM2.Stmt Γ Λ σ) (v : σ) (S R : Words Γ) (j : ℕ)
    (h : AgreeCone (radius q) j S R) :
    (wordStepAux q v S).label = (wordStepAux q v R).label ∧
    (wordStepAux q v S).var = (wordStepAux q v R).var ∧
    ∀ k, (wordStepAux q v S).stk k j = (wordStepAux q v R).stk k j := by
  induction q generalizing v S R with
  | push k f q ih => exact ih _ _ _ (agreeCone_push h k (f v))
  | peek k f q ih =>
    have hh := agreeCone_head h k
    simp only [wordStepAux, hh]
    exact ih _ _ _ (agreeCone_mono (Nat.le_succ _) h)
  | pop k f q ih =>
    have hh := agreeCone_head h k
    simp only [wordStepAux, hh]
    exact ih _ _ _ (agreeCone_pop h k)
  | load f q ih => exact ih _ _ _ h
  | branch f q r iq ir =>
    cases hf : f v
    · simpa only [wordStepAux, hf, Bool.false_eq_true, ↓reduceIte] using
        ir v S R (agreeCone_mono (Nat.le_max_right _ _) h)
    · simpa only [wordStepAux, hf, ↓reduceIte] using
        iq v S R (agreeCone_mono (Nat.le_max_left _ _) h)
  | goto f => exact ⟨rfl,rfl,fun k => h k j (Or.inr ⟨by omega,by omega⟩)⟩
  | halt => exact ⟨rfl,rfl,fun k => h k j (Or.inr ⟨by omega,by omega⟩)⟩

end DirectedFeedback.CookLevin

namespace DirectedFeedback.CookLevin
open Turing
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

theorem stepAux_length (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k))
    (B : ℕ) (hS : ∀ k, (S k).length ≤ B) :
    ∀ k, ((TM2.stepAux q v S).stk k).length ≤ B + radius q := by
  induction q generalizing v S B with
  | push k f q ih =>
    have hs : ∀ j, ((Function.update S k (f v :: S k)) j).length ≤ B+1 := by
      intro j
      by_cases hj : j = k
      · subst j; simpa only [Function.update_self, List.length_cons] using Nat.add_le_add_right (hS k) 1
      · rw [Function.update_of_ne hj]; exact (hS j).trans (Nat.le_succ B)
    intro j
    have hh := ih v _ (B+1) hs j
    simpa only [TM2.stepAux, radius, Nat.add_assoc, Nat.add_comm 1] using hh
  | peek k f q ih =>
    intro j
    exact (ih (f v (S k).head?) S B hS j).trans (by simp [radius])
  | pop k f q ih =>
    have hs : ∀ j, ((Function.update S k (S k).tail) j).length ≤ B := by
      intro j
      by_cases hj : j = k
      · subst j; simp only [Function.update_self, List.length_tail]; exact (Nat.sub_le _ _).trans (hS k)
      · rw [Function.update_of_ne hj]; exact hS j
    intro j
    exact (ih (f v (S k).head?) _ B hs j).trans (by simp [radius])
  | load f q ih => exact ih (f v) S B hS
  | branch f q r iq ir =>
    intro j
    cases hf : f v
    · simp only [TM2.stepAux, hf]
      exact (ir v S B hS j).trans (Nat.add_le_add_left (Nat.le_max_right _ _) B)
    · simp only [TM2.stepAux, hf]
      exact (iq v S B hS j).trans (Nat.add_le_add_left (Nat.le_max_left _ _) B)
  | goto f => simpa only [TM2.stepAux, radius, Nat.add_zero] using hS
  | halt => simpa only [TM2.stepAux, radius, Nat.add_zero] using hS

def cfgNext (M : Λ → TM2.Stmt Γ Λ σ) (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ σ :=
  match c.l with
  | none => c
  | some l => TM2.stepAux (M l) c.var c.stk

def wordNext (M : Λ → TM2.Stmt Γ Λ σ) (c : WordCfg Γ Λ σ) : WordCfg Γ Λ σ :=
  match c.label with
  | none => c
  | some l => wordStepAux (M l) c.var c.stk

theorem wordNext_ofCfg (M : Λ → TM2.Stmt Γ Λ σ) (c : TM2.Cfg Γ Λ σ) :
    wordNext M (WordCfg.ofCfg c) = WordCfg.ofCfg (cfgNext M c) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l => exact wordStepAux_ofLists (M l) v S

noncomputable def programRadius [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ) : ℕ :=
  Finset.univ.sup (fun l => radius (M l))

omit [DecidableEq K] in
theorem radius_le_programRadius [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ) (l : Λ) :
    radius (M l) ≤ programRadius M := Finset.le_sup (f := fun l => radius (M l)) (Finset.mem_univ l)

theorem cfgNext_length [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ)
    (c : TM2.Cfg Γ Λ σ) (B : ℕ) (hc : ∀ k, (c.stk k).length ≤ B) :
    ∀ k, ((cfgNext M c).stk k).length ≤ B + programRadius M := by
  cases c with
  | mk l v S =>
    cases l with
    | none => exact fun k => (hc k).trans (Nat.le_add_right _ _)
    | some l =>
      exact fun k => (stepAux_length (M l) v S B hc k).trans
        (Nat.add_le_add_left (radius_le_programRadius M l) B)

theorem cfgRun_length [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ)
    (c : TM2.Cfg Γ Λ σ) (B t : ℕ) (hc : ∀ k, (c.stk k).length ≤ B) :
    ∀ k, (((cfgNext M)^[t] c).stk k).length ≤ B + t * programRadius M := by
  induction t with
  | zero => simpa using hc
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    have hh := cfgNext_length M ((cfgNext M)^[t] c) (B+t*programRadius M) ih
    simpa only [Nat.succ_mul, Nat.add_assoc] using hh

structure Window (Γ : K → Type) (Λ σ : Type) (S : ℕ) where
  label : Option Λ
  var : σ
  stk : ∀ k, Fin S → Option (Γ k)

def Window.words {S : ℕ} (c : Window Γ Λ σ S) : WordCfg Γ Λ σ :=
  ⟨c.label,c.var,fun k i => if h : i < S then c.stk k ⟨i,h⟩ else none⟩

def Window.ofCfg (S : ℕ) (c : TM2.Cfg Γ Λ σ) : Window Γ Λ σ S :=
  ⟨c.l,c.var,fun k i => (c.stk k)[i.val]?⟩

omit [DecidableEq K] in
theorem Window.words_ofCfg (S : ℕ) (c : TM2.Cfg Γ Λ σ)
    (hc : ∀ k, (c.stk k).length ≤ S) :
    (Window.ofCfg S c).words = WordCfg.ofCfg c := by
  unfold Window.words Window.ofCfg WordCfg.ofCfg
  congr 1
  funext k i
  by_cases hi : i < S
  · simp [wordsOfLists, hi]
  · simp only [dite_eq_right hi, wordsOfLists]
    exact (List.getElem?_eq_none ((hc k).trans (Nat.le_of_not_gt hi))).symm

def Follows (M : Λ → TM2.Stmt Γ Λ σ) {S : ℕ} (a b : Window Γ Λ σ S) : Prop :=
  let next := wordNext M a.words
  b.label = next.label ∧ b.var = next.var ∧ ∀ k i, b.stk k i = next.stk k i.val

theorem window_follows [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ)
    (c : TM2.Cfg Γ Λ σ) (B S : ℕ) (hc : ∀ k, (c.stk k).length ≤ B)
    (hBS : B + programRadius M ≤ S) :
    Follows M (Window.ofCfg S c) (Window.ofCfg S (cfgNext M c)) := by
  unfold Follows
  rw [Window.words_ofCfg S c (fun k => (hc k).trans (by omega)), wordNext_ofCfg]
  exact ⟨rfl,rfl,fun _ _ => rfl⟩

theorem window_follows_unique (M : Λ → TM2.Stmt Γ Λ σ) {S : ℕ}
    (a b c : Window Γ Λ σ S) (hb : Follows M a b) (hc : Follows M a c) : b = c := by
  cases b with
  | mk bl bv bs =>
    cases c with
    | mk cl cv cs =>
      obtain ⟨hl,hv,hs⟩ := hb
      obtain ⟨hl',hv',hs'⟩ := hc
      have hs'' : bs = cs := funext (fun k => funext (fun i => (hs k i).trans (hs' k i).symm))
      cases hl.trans hl'.symm
      cases hv.trans hv'.symm
      cases hs''
      rfl

theorem wordNext_local [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ)
    (a b : WordCfg Γ Λ σ) (j : ℕ) (hl : a.label = b.label) (hv : a.var = b.var)
    (hS : AgreeCone (programRadius M) j a.stk b.stk) :
    (wordNext M a).label = (wordNext M b).label ∧
    (wordNext M a).var = (wordNext M b).var ∧
    ∀ k, (wordNext M a).stk k j = (wordNext M b).stk k j := by
  cases a with
  | mk al av aS =>
    cases b with
    | mk bl bv bS =>
      dsimp only at hl hv hS ⊢
      subst bl; subst bv
      cases al with
      | none => exact ⟨rfl,rfl,fun k => hS k j (Or.inr ⟨by omega,by omega⟩)⟩
      | some l =>
        exact wordStepAux_local (M l) av aS bS j
          (agreeCone_mono (radius_le_programRadius M l) hS)

end DirectedFeedback.CookLevin

namespace DirectedFeedback.CookLevin
open Turing
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

theorem trace_unique [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ)
    (initial : TM2.Cfg Γ Λ σ) (B H S : ℕ)
    (hinit : ∀ k, (initial.stk k).length ≤ B)
    (hcap : B + H*programRadius M ≤ S)
    (trace : Fin (H+1) → Window Γ Λ σ S)
    (hzero : trace 0 = Window.ofCfg S initial)
    (hstep : ∀ t : Fin H, Follows M (trace t.castSucc) (trace t.succ)) :
    ∀ t : Fin (H+1), trace t = Window.ofCfg S ((cfgNext M)^[t.val] initial) := by
  intro t
  induction t using Fin.induction with
  | zero => simpa only [Fin.val_zero, Function.iterate_zero, id_eq] using hzero
  | succ t ih =>
    apply window_follows_unique M (trace t.castSucc) _ _ (hstep t)
    rw [ih]
    change Follows M (Window.ofCfg S ((cfgNext M)^[t.val] initial))
      (Window.ofCfg S ((cfgNext M)^[t.val+1] initial))
    rw [Function.iterate_succ_apply']
    apply window_follows M _ (B+t.val*programRadius M) S
      (cfgRun_length M initial B t.val hinit)
    have ht : t.val+1 ≤ H := t.isLt
    have hm := Nat.mul_le_mul_right (programRadius M) ht
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using
      le_trans (Nat.add_le_add_left hm B) hcap

omit [DecidableEq K] in
theorem iterate_partial_none {α : Type} (f : α → Option α) (n : ℕ) :
    (fun p : Option α => p.bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

omit [DecidableEq K] in

theorem iterate_partial_some {α : Type} (f : α → Option α) (n : ℕ) (a b : α)
    (h : (fun p : Option α => p.bind f)^[n] (some a) = some b) :
    (fun x => (f x).getD x)^[n] a = b := by
  induction n generalizing a with
  | zero => exact Option.some.inj h
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    cases hf : f a with
    | none =>
      simp only [Option.bind_some, hf, iterate_partial_none] at h
      contradiction
    | some c =>
      simp only [Option.bind_some, hf] at h
      simpa only [hf, Option.getD_some] using ih c h

theorem cfgNext_eq_getD (M : Λ → TM2.Stmt Γ Λ σ) (c : TM2.Cfg Γ Λ σ) :
    cfgNext M c = (TM2.step M c).getD c := by
  cases c with
  | mk l v S => cases l <;> rfl

theorem output_run (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    (output : List (tm.Γ tm.k₁)) (H : ℕ)
    (h : TM2OutputsInTime tm input (some output) H) :
    (cfgNext tm.m)^[H] (initList tm input) = haltList tm output := by
  rcases h with ⟨⟨n,hn⟩,hle⟩
  have hr := iterate_partial_some tm.step n (initList tm input) (haltList tm output) hn
  have he : (fun x => (tm.step x).getD x) = cfgNext tm.m := by
    funext c
    exact (cfgNext_eq_getD tm.m c).symm
  rw [he] at hr
  have hfix : cfgNext tm.m (haltList tm output) = haltList tm output := rfl
  have hmore := Function.iterate_add_apply (cfgNext tm.m) (H-n) n (initList tm input)
  unfold FinTM2.Cfg at *
  rw [Nat.sub_add_cancel hle,hr,Function.iterate_fixed hfix] at hmore
  exact hmore

end DirectedFeedback.CookLevin

namespace DirectedFeedback.CookLevin
open Turing
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

abbrev StackAtom (Γ : K → Type) := ∀ k, Option (Γ k)
abbrev Atom (Γ : K → Type) (Λ σ : Type) := (Option Λ × σ) × StackAtom Γ
abbrev Row (Γ : K → Type) (Λ σ : Type) (S : ℕ) := Fin (S+1) → Atom Γ Λ σ

def rowWindow {S : ℕ} (row : Row Γ Λ σ S) : Window Γ Λ σ S where
  label := (row 0).1.1
  var := (row 0).1.2
  stk := fun k j => (row j.succ).2 k

def windowRow {S : ℕ} (w : Window Γ Λ σ S) : Row Γ Λ σ S :=
  Fin.cases ((w.label,w.var), fun _ => none)
    (fun j => ((w.label,w.var), fun k => w.stk k j))

omit [DecidableEq K] in
@[simp] theorem rowWindow_windowRow {S : ℕ} (w : Window Γ Λ σ S) :
    rowWindow (windowRow w) = w := by
  cases w
  rfl

@[ext] structure LocalData (Γ : K → Type) (Λ σ : Type) (r : ℕ) where
  ctrl : Option Λ × σ
  head : Fin r → StackAtom Γ
  band : Fin (2*r+1) → StackAtom Γ

def LocalData.wordCfg {r : ℕ} (d : LocalData Γ Λ σ r) (j : ℕ) : WordCfg Γ Λ σ where
  label := d.ctrl.1
  var := d.ctrl.2
  stk := fun k i =>
    if hi : i < r then d.head ⟨i,hi⟩ k
    else if hb : j-r ≤ i ∧ i < j-r+(2*r+1) then d.band ⟨i-(j-r),by omega⟩ k
    else none

def localData (r j : ℕ) (w : WordCfg Γ Λ σ) : LocalData Γ Λ σ r where
  ctrl := (w.label,w.var)
  head := fun i k => w.stk k i.val
  band := fun i k => w.stk k (j-r+i.val)

omit [DecidableEq K] in
theorem localData_agree (r j : ℕ) (w : WordCfg Γ Λ σ) :
    AgreeCone r j (localData r j w |>.wordCfg j).stk w.stk := by
  intro k i hi
  dsimp [LocalData.wordCfg,localData]
  split_ifs with hh hb
  · rfl
  · congr 1
    omega
  · exfalso
    rcases hi with hi | ⟨h₁,h₂⟩
    · exact hh hi
    · apply hb
      omega

theorem localData_next [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ)
    (j : ℕ) (w : WordCfg Γ Λ σ) :
    (wordNext M (localData (programRadius M) j w |>.wordCfg j)).label = (wordNext M w).label ∧
    (wordNext M (localData (programRadius M) j w |>.wordCfg j)).var = (wordNext M w).var ∧
    ∀ k, (wordNext M (localData (programRadius M) j w |>.wordCfg j)).stk k j =
      (wordNext M w).stk k j :=
  wordNext_local M _ _ j rfl rfl (localData_agree _ _ _)

abbrev StepSlot (r : ℕ) := Fin r ⊕ (Fin (2*r+1) ⊕ Fin 3)
abbrev TracePosition (H S : ℕ) := Fin (H+1) × Fin (S+1)

def cellAddress (S i : ℕ) : Fin (S+1) := if h : i < S then ⟨i+1,by omega⟩ else 0

def stepQuery {H S r : ℕ} (t : Fin H) (j : Fin (S+1)) :
    StepSlot r → TracePosition H S
  | .inl i => (t.castSucc,cellAddress S i.val)
  | .inr (.inl i) => (t.castSucc,cellAddress S (j.val-r+i.val))
  | .inr (.inr i) => if i.val = 0 then (t.castSucc,0)
    else if i.val = 1 then (t.succ,0) else (t.succ,cellAddress S j.val)

def dataOfQueries {S r : ℕ} (j : Fin (S+1))
    (a : StepSlot r → Atom Γ Λ σ) : LocalData Γ Λ σ r where
  ctrl := (a (.inr (.inr 0))).1
  head := fun i k => if i.val < S then (a (.inl i)).2 k else none
  band := fun i k => if j.val-r+i.val < S then (a (.inr (.inl i))).2 k else none

noncomputable def stepAccepts [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ)
    {S : ℕ} (j : Fin (S+1)) (a : StepSlot (programRadius M) → Atom Γ Λ σ) : Bool := by
  classical
  let w := wordNext M ((dataOfQueries j a).wordCfg j.val)
  exact decide ((a (.inr (.inr 1))).1 = (w.label,w.var) ∧
    (j.val < S → ∀ k, (a (.inr (.inr 2))).2 k = w.stk k j.val))

omit [DecidableEq K] in
theorem dataOfQueries_eq {H S r : ℕ} (A : TracePosition H S → Atom Γ Λ σ)
    (t : Fin H) (j : Fin (S+1)) :
    dataOfQueries j (A ∘ stepQuery (r:=r) t j) =
      localData r j.val (rowWindow (fun p => A (t.castSucc,p))).words := by
  apply LocalData.ext
  · rfl
  · funext i k
    dsimp [dataOfQueries,localData,Window.words,rowWindow,stepQuery,cellAddress]
    split_ifs with hi <;> rfl
  · funext i k
    dsimp [dataOfQueries,localData,Window.words,rowWindow,stepQuery,cellAddress]
    split_ifs with hi <;> rfl

theorem stepAccepts_iff [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ)
    {H S : ℕ} (A : TracePosition H S → Atom Γ Λ σ)
    (t : Fin H) (j : Fin (S+1)) :
    stepAccepts M j (A ∘ stepQuery t j) = true ↔
      let old := rowWindow (fun p => A (t.castSucc,p))
      let next := rowWindow (fun p => A (t.succ,p))
      next.label = (wordNext M old.words).label ∧
      next.var = (wordNext M old.words).var ∧
      (j.val < S → ∀ k, (A (t.succ,cellAddress S j.val)).2 k =
         (wordNext M old.words).stk k j.val) := by
  classical
  dsimp [stepAccepts]
  rw [decide_eq_true_eq,dataOfQueries_eq]
  have h := localData_next M j.val (rowWindow (fun p => A (t.castSucc,p))).words
  simp only [h.1,h.2.1,h.2.2,stepQuery]
  norm_num [rowWindow,Prod.ext_iff,and_assoc]

theorem stepAccepts_all_iff [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ)
    {H S : ℕ} (A : TracePosition H S → Atom Γ Λ σ) (t : Fin H) :
    (∀ j, stepAccepts M j (A ∘ stepQuery t j) = true) ↔
      Follows M (rowWindow (fun p => A (t.castSucc,p)))
        (rowWindow (fun p => A (t.succ,p))) := by
  simp only [stepAccepts_iff]
  constructor
  · intro h
    refine ⟨(h 0).1,(h 0).2.1,?_⟩
    intro k j
    have hh := (h j.castSucc).2.2 j.isLt k
    simpa only [cellAddress,Fin.val_castSucc,j.isLt,↓reduceDIte,rowWindow,Fin.succ] using hh
  · rintro ⟨hl,hv,hs⟩ j
    refine ⟨hl,hv,?_⟩
    intro hj k
    simpa only [cellAddress,hj,↓reduceDIte,rowWindow,Fin.succ,Nat.add_comm] using hs k ⟨j.val,hj⟩

end DirectedFeedback.CookLevin

namespace DirectedFeedback.CookLevin

def prefixList {α : Type} : ℕ → (ℕ → Option α) → List α
  | 0, _ => []
  | n+1,w => match w 0 with
    | none => []
    | some a => a :: prefixList n (fun i => w (i+1))

theorem prefixList_length {α : Type} (n : ℕ) (w : ℕ → Option α) :
    (prefixList n w).length ≤ n := by
  induction n generalizing w with
  | zero => simp [prefixList]
  | succ n ih =>
    dsimp [prefixList]
    cases h : w 0 with
    | none => simp
    | some a => simpa using Nat.succ_le_succ (ih (fun i => w (i+1)))

def NoHoles {α : Type} (w : ℕ → Option α) : Prop :=
  ∀ i, w i = none → w (i+1) = none

theorem NoHoles.tail {α : Type} {w : ℕ → Option α} (h : NoHoles w) :
    NoHoles (fun i => w (i+1)) := fun i => h (i+1)

theorem NoHoles.propagate {α : Type} {w : ℕ → Option α} (h : NoHoles w)
    (i j : ℕ) (hij : i ≤ j) (hi : w i = none) : w j = none := by
  induction j, hij using Nat.le_induction with
  | base => exact hi
  | succ j hj ih => exact h j ih

theorem prefixList_getElem? {α : Type} (n : ℕ) (w : ℕ → Option α)
    (h : NoHoles w) (i : ℕ) (hi : i < n) :
    (prefixList n w)[i]? = w i := by
  induction n generalizing w i with
  | zero => omega
  | succ n ih =>
    cases h0 : w 0 with
    | none =>
      rw [prefixList,h0]
      exact (h.propagate 0 i (Nat.zero_le _) h0).symm
    | some a =>
      rw [prefixList,h0]
      cases i with
      | zero => simpa using h0.symm
      | succ i =>
        simpa using ih (fun i => w (i+1)) h.tail i (by omega)

theorem prefixList_getElem?_all {α : Type} (n : ℕ) (w : ℕ → Option α)
    (h : NoHoles w) (hbound : ∀ i, n ≤ i → w i = none) (i : ℕ) :
    (prefixList n w)[i]? = w i := by
  by_cases hi : i < n
  · exact prefixList_getElem? n w h i hi
  · rw [List.getElem?_eq_none ((prefixList_length n w).trans (by omega)),hbound i (by omega)]

theorem list_getElem?_noHoles {α : Type} (l : List α) : NoHoles (fun i => l[i]?) := by
  intro i hi
  exact List.getElem?_eq_none (by have := List.getElem?_eq_none_iff.mp hi; omega)

theorem reconstruct_suffix {α : Type} (pref : List α) (C : ℕ) (w : ℕ → Option α)
    (hp : ∀ i, i < pref.length → w i = pref[i]?)
    (ht : ∀ i, pref.length + C ≤ i → w i = none)
    (hn : ∀ i, pref.length ≤ i → w i = none → w (i+1) = none) :
    ∃ certificate : List α, certificate.length ≤ C ∧
      ∀ i, (pref ++ certificate)[i]? = w i := by
  let suffix := fun i => w (pref.length+i)
  have hs : NoHoles suffix := by
    intro i hi
    simpa only [suffix,Nat.add_assoc] using hn (pref.length+i) (by omega) hi
  refine ⟨prefixList C suffix,prefixList_length C suffix,?_⟩
  intro i
  by_cases hi : i < pref.length
  · rw [List.getElem?_append_left hi,hp i hi]
  · have hi' : pref.length ≤ i := by omega
    rw [List.getElem?_append_right hi']
    rw [prefixList_getElem?_all C suffix hs]
    · dsimp [suffix]
      congr 1
      omega
    · intro j hj
      exact ht (pref.length+j) (by omega)

end DirectedFeedback.CookLevin

namespace DirectedFeedback.CookLevin
open Turing

def InitialConditions (tm : FinTM2) (pref : List (tm.Γ tm.k₀)) (C : ℕ)
    (w : WordCfg tm.Γ tm.Λ tm.σ) : Prop :=
  w.label = some tm.main ∧ w.var = tm.initialState ∧
  (∀ k, k ≠ tm.k₀ → ∀ i, w.stk k i = none) ∧
  (∀ i, i < pref.length → w.stk tm.k₀ i = pref[i]?) ∧
  (∀ i, pref.length+C ≤ i → w.stk tm.k₀ i = none) ∧
  (∀ i, pref.length ≤ i → w.stk tm.k₀ i = none → w.stk tm.k₀ (i+1) = none)

def initialPredicate (tm : FinTM2) (pref : List (tm.Γ tm.k₀)) (C i : ℕ)
    (ctrl : Option tm.Λ × tm.σ) (current next : StackAtom tm.Γ) : Prop :=
  ctrl = (some tm.main,tm.initialState) ∧
  (∀ k, k ≠ tm.k₀ → current k = none) ∧
  (i < pref.length → current tm.k₀ = pref[i]?) ∧
  (pref.length+C ≤ i → current tm.k₀ = none) ∧
  (pref.length ≤ i → current tm.k₀ = none → next tm.k₀ = none)

def initialQuery {H S : ℕ} (j : Fin (S+1)) : Fin 3 → TracePosition H S := fun i =>
  if i.val = 0 then (0,0) else if i.val = 1 then (0,cellAddress S j.val)
  else (0,cellAddress S (j.val+1))

noncomputable def initialAccepts (tm : FinTM2) (pref : List (tm.Γ tm.k₀)) (C : ℕ)
    {S : ℕ} (j : Fin (S+1)) (a : Fin 3 → Atom tm.Γ tm.Λ tm.σ) : Bool := by
  classical
  exact decide (initialPredicate tm pref C j.val (a 0).1
    (fun k => if j.val < S then (a 1).2 k else none)
    (fun k => if j.val+1 < S then (a 2).2 k else none))

theorem row_cell_query (tm : FinTM2) {H S : ℕ}
    (A : TracePosition H S → Atom tm.Γ tm.Λ tm.σ) (t : Fin (H+1)) (i : ℕ) :
    (fun k => if i < S then (A (t,cellAddress S i)).2 k else none) =
      (fun k => (rowWindow (fun p => A (t,p))).words.stk k i) := by
  funext k
  dsimp [cellAddress,rowWindow,Window.words]
  split_ifs with hi <;> rfl

theorem initialAccepts_iff (tm : FinTM2) (pref : List (tm.Γ tm.k₀)) (C : ℕ)
    {H S : ℕ} (A : TracePosition H S → Atom tm.Γ tm.Λ tm.σ) (j : Fin (S+1)) :
    initialAccepts tm pref C j (A ∘ initialQuery j) = true ↔
      let w := (rowWindow (fun p => A (0,p))).words
      initialPredicate tm pref C j.val (w.label,w.var)
        (fun k => w.stk k j.val) (fun k => w.stk k (j.val+1)) := by
  classical
  dsimp [initialAccepts]
  rw [decide_eq_true_eq]
  change initialPredicate tm pref C j.val (A (0,0)).1
    (fun k => if j.val < S then (A (0,cellAddress S j.val)).2 k else none)
    (fun k => if j.val+1 < S then (A (0,cellAddress S (j.val+1))).2 k else none) ↔ _
  rw [row_cell_query tm A 0 j.val,row_cell_query tm A 0 (j.val+1)]
  rfl

theorem initialAccepts_all_iff (tm : FinTM2) (pref : List (tm.Γ tm.k₀)) (C : ℕ)
    {H S : ℕ} (hS : pref.length+C ≤ S)
    (A : TracePosition H S → Atom tm.Γ tm.Λ tm.σ) :
    (∀ j, initialAccepts tm pref C j (A ∘ initialQuery j) = true) ↔
      InitialConditions tm pref C (rowWindow (fun p => A (0,p))).words := by
  simp only [initialAccepts_iff]
  constructor
  · intro h
    have hc := (h 0).1
    refine ⟨(congrArg Prod.fst hc),(congrArg Prod.snd hc),?_,?_,?_,?_⟩
    · intro k hk i
      by_cases hi : i < S
      · exact (h ⟨i,by omega⟩).2.1 k hk
      · simp [Window.words,hi]
    · intro i hi
      exact (h ⟨i,by omega⟩).2.2.1 hi
    · intro i hi
      by_cases hiS : i < S
      · exact (h ⟨i,by omega⟩).2.2.2.1 hi
      · simp [Window.words,hiS]
    · intro i hi hnone
      by_cases hiS : i < S
      · exact (h ⟨i,by omega⟩).2.2.2.2 hi hnone
      · simp [Window.words,show ¬i+1 < S by omega]
  · rintro ⟨hl,hv,hk,hp,ht,hn⟩ j
    exact ⟨Prod.ext hl hv,fun k h => hk k h j.val,hp j.val,ht j.val,hn j.val⟩

theorem initial_reconstruct (tm : FinTM2) (pref : List (tm.Γ tm.k₀)) (C S : ℕ)
    (w : Window tm.Γ tm.Λ tm.σ S) (h : InitialConditions tm pref C w.words) :
    ∃ certificate : List (tm.Γ tm.k₀), certificate.length ≤ C ∧
      w = Window.ofCfg S (initList tm (pref ++ certificate)) := by
  obtain ⟨hl,hv,hk,hp,ht,hn⟩ := h
  obtain ⟨certificate,hC,he⟩ := reconstruct_suffix pref C (w.words.stk tm.k₀) hp ht hn
  refine ⟨certificate,hC,?_⟩
  cases w with
  | mk label var stk =>
    dsimp [Window.words] at hl hv
    subst label; subst var
    congr 1
    funext k i
    by_cases hkk : k = tm.k₀
    · subst k
      have hh := he i.val
      simpa [Window.words,Window.ofCfg,initList,i.isLt] using hh.symm
    · have hh := hk k hkk i.val
      simpa [Window.words,Window.ofCfg,initList,i.isLt,hkk] using hh

theorem initial_real (tm : FinTM2) (pref certificate : List (tm.Γ tm.k₀)) (C S : ℕ)
    (hC : certificate.length ≤ C) (hS : pref.length+C ≤ S) :
    InitialConditions tm pref C (Window.ofCfg S (initList tm (pref ++ certificate))).words := by
  have hb : ∀ k, ((initList tm (pref ++ certificate)).stk k).length ≤ S := by
    intro k
    dsimp [initList]
    split_ifs with hk
    · subst k; change (pref ++ certificate).length ≤ S
      simp only [List.length_append]; omega
    · simp
  rw [Window.words_ofCfg S _ hb]
  refine ⟨rfl,rfl,?_,?_,?_,?_⟩
  · intro k hk i
    simp [WordCfg.ofCfg,wordsOfLists,initList,hk]
  · intro i hi
    simp [WordCfg.ofCfg,wordsOfLists,initList,List.getElem?_append_left hi]
  · intro i hi
    simp [WordCfg.ofCfg,wordsOfLists,initList,
      List.getElem?_eq_none (show (pref++certificate).length ≤ i by simp only [List.length_append]; omega)]
  · intro i _ hi
    have hh : NoHoles (fun i => (pref++certificate)[i]?) := list_getElem?_noHoles _
    simpa [WordCfg.ofCfg,wordsOfLists,initList] using hh i (by
      simpa [WordCfg.ofCfg,wordsOfLists,initList] using hi)

end DirectedFeedback.CookLevin

namespace DirectedFeedback.CookLevin

structure LocalCSP (Alphabet Variable Event Slot : Type) where
  query : Event → Slot → Variable
  accepts : Event → (Slot → Alphabet) → Bool

def LocalCSP.Satisfiable {A I E J : Type} (C : LocalCSP A I E J) : Prop :=
  ∃ assignment : I → A, ∀ e, C.accepts e (assignment ∘ C.query e) = true

structure FiniteCodec (A : Type) where
  width : ℕ
  encode : A → (Fin width → Bool)
  decode : (Fin width → Bool) → A
  decode_encode : ∀ a, decode (encode a) = a

noncomputable def oneHotCodec (A : Type) [Fintype A] [Nonempty A] : FiniteCodec A := by
  classical
  let enc : A → (Fin (Fintype.card A) → Bool) := fun a i =>
    decide ((Fintype.equivFin A).symm i = a)
  have hinj : Function.Injective enc := by
    intro a b hab
    have he := congrFun hab ((Fintype.equivFin A) a)
    simpa [enc] using he
  exact {
    width := Fintype.card A
    encode := enc
    decode := fun bits => if h : ∃ a, enc a = bits then h.choose else Classical.choice inferInstance
    decode_encode := fun a => by
      split_ifs with h
      · exact hinj h.choose_spec
      · exact False.elim (h ⟨a,rfl⟩) }

def LocalCSP.booleanize {A I E J : Type} (C : LocalCSP A I E J) (codec : FiniteCodec A) :
    LocalCSP Bool (I × Fin codec.width) E (J × Fin codec.width) where
  query := fun e j => (C.query e j.1,j.2)
  accepts := fun e pattern => C.accepts e (fun j => codec.decode (fun b => pattern (j,b)))

theorem LocalCSP.booleanize_satisfiable_iff {A I E J : Type}
    (C : LocalCSP A I E J) (codec : FiniteCodec A) :
    (C.booleanize codec).Satisfiable ↔ C.Satisfiable := by
  constructor
  · rintro ⟨B,hB⟩
    exact ⟨fun i => codec.decode (fun b => B (i,b)),hB⟩
  · rintro ⟨A,hA⟩
    refine ⟨fun i => codec.encode (A i.1) i.2,?_⟩
    intro e
    simpa only [booleanize,Function.comp_def,codec.decode_encode] using hA e

def LocalCSP.reindex {A I E J I' E' J' : Type} (C : LocalCSP A I E J)
    (v : I ≃ I') (e : E ≃ E') (s : J ≃ J') : LocalCSP A I' E' J' where
  query := fun event slot => v (C.query (e.symm event) (s.symm slot))
  accepts := fun event pattern => C.accepts (e.symm event) (pattern ∘ s)

theorem LocalCSP.reindex_satisfiable_iff {A I E J I' E' J' : Type}
    (C : LocalCSP A I E J) (v : I ≃ I') (e : E ≃ E') (s : J ≃ J') :
    (C.reindex v e s).Satisfiable ↔ C.Satisfiable := by
  constructor
  · rintro ⟨assignment,h⟩
    refine ⟨assignment ∘ v,?_⟩
    intro event
    simpa only [reindex,Function.comp_def,Equiv.symm_apply_apply] using h (e event)
  · rintro ⟨assignment,h⟩
    refine ⟨assignment ∘ v.symm,?_⟩
    intro event
    simpa only [reindex,Function.comp_def,Equiv.symm_apply_apply] using h (e.symm event)

noncomputable def LocalCSP.pad {A I E J : Type} [Nonempty I] (C : LocalCSP A I E J) (P : Type) :
    LocalCSP A I E (J ⊕ P) := by
  classical
  exact ⟨fun e => Sum.elim (C.query e) (fun _ => Classical.choice inferInstance),
    fun e pattern => C.accepts e (pattern ∘ Sum.inl)⟩

theorem LocalCSP.pad_satisfiable_iff {A I E J : Type} [Nonempty I]
    (C : LocalCSP A I E J) (P : Type) : (C.pad P).Satisfiable ↔ C.Satisfiable := Iff.rfl

end DirectedFeedback.CookLevin

namespace DirectedFeedback.CookLevin
open Turing
attribute [local instance] FinTM2.ΛFin
abbrev TableauEvent (H S : ℕ) := Fin (S+1) ⊕ ((Fin H × Fin (S+1)) ⊕ Unit)
abbrev TableauSlot (tm : FinTM2) := Fin 3 ⊕ (StepSlot (programRadius tm.m) ⊕ Unit)

noncomputable def tableauQuery (tm : FinTM2) {H S : ℕ} :
    TableauEvent H S → TableauSlot tm → TracePosition H S
  | .inl j, .inl i => initialQuery j i
  | .inr (.inl (t,j)), .inr (.inl i) => stepQuery t j i
  | .inr (.inr _), .inr (.inr _) => (Fin.last H,cellAddress S 0)
  | _, _ => (0,0)

noncomputable def tableau (tm : FinTM2) (pref : List (tm.Γ tm.k₀)) (C H S : ℕ)
    (out : tm.Γ tm.k₁) : LocalCSP (Atom tm.Γ tm.Λ tm.σ)
      (TracePosition H S) (TableauEvent H S) (TableauSlot tm) where
  query := tableauQuery tm
  accepts := fun e a => match e with
    | .inl j => initialAccepts tm pref C j (a ∘ Sum.inl)
    | .inr (.inl (_,j)) => stepAccepts tm.m j (a ∘ Sum.inr ∘ Sum.inl)
    | .inr (.inr _) => by
      classical
      exact decide ((a (.inr (.inr ()))).2 tm.k₁ = some out)

theorem tableau_satisfiable_iff (tm : FinTM2) (pref : List (tm.Γ tm.k₀))
    (C H S : ℕ) (hS : pref.length+C+H*programRadius tm.m ≤ S) (hpos : 0 < S)
    (out : tm.Γ tm.k₁) :
    (tableau tm pref C H S out).Satisfiable ↔
      ∃ cert : List (tm.Γ tm.k₀), cert.length ≤ C ∧
      (((cfgNext tm.m)^[H] (initList tm (pref++cert))).stk tm.k₁)[0]? = some out := by
  classical
  constructor
  · rintro ⟨A,hA⟩
    have hi : InitialConditions tm pref C (rowWindow (fun p => A (0,p))).words :=
      (initialAccepts_all_iff tm pref C (by omega) A).mp (fun j => hA (.inl j))
    obtain ⟨cert,hc,hz⟩ := initial_reconstruct tm pref C S _ hi
    have hs : ∀ t : Fin H, Follows tm.m (rowWindow (fun p => A (t.castSucc,p)))
        (rowWindow (fun p => A (t.succ,p))) := by
      intro t
      exact (stepAccepts_all_iff tm.m A t).mp (fun j => hA (.inr (.inl (t,j))))
    have hb : ∀ k, ((initList tm (pref++cert)).stk k).length ≤ pref.length+C := by
      intro k
      dsimp [initList]
      split_ifs with hk
      · subst k; change (pref++cert).length ≤ pref.length+C
        simpa only [List.length_append] using Nat.add_le_add_left hc pref.length
      · simp
    have ht := trace_unique tm.m (initList tm (pref++cert)) (pref.length+C) H S hb hS
      (fun t => rowWindow (fun p => A (t,p))) hz hs (Fin.last H)
    have hf := hA (.inr (.inr ()))
    change decide ((A (Fin.last H,cellAddress S 0)).2 tm.k₁ = some out) = true at hf
    rw [decide_eq_true_eq] at hf
    have hh := congrArg (fun w : Window tm.Γ tm.Λ tm.σ S => w.stk tm.k₁ ⟨0,hpos⟩) ht
    simp only [rowWindow,Window.ofCfg,Fin.val_last] at hh
    refine ⟨cert,hc,?_⟩
    rw [← hh]
    simpa only [cellAddress,hpos,↓reduceDIte,Fin.succ] using hf
  · rintro ⟨cert,hc,hout⟩
    let c : TM2.Cfg tm.Γ tm.Λ tm.σ := initList tm (pref++cert)
    have hb : ∀ k, (c.stk k).length ≤ pref.length+C := by
      intro k
      dsimp [c,initList]
      split_ifs with hk
      · subst k; change (pref++cert).length ≤ pref.length+C
        simpa only [List.length_append] using Nat.add_le_add_left hc pref.length
      · simp
    let tr : Fin (H+1) → Window tm.Γ tm.Λ tm.σ S := fun t =>
      Window.ofCfg S ((cfgNext tm.m)^[t.val] c)
    let A : TracePosition H S → Atom tm.Γ tm.Λ tm.σ := fun p => windowRow (tr p.1) p.2
    have he (t : Fin (H+1)) : rowWindow (fun p => A (t,p)) = tr t := rowWindow_windowRow _
    refine ⟨A,?_⟩
    intro e
    rcases e with j | (⟨t,j⟩ | u)
    · change initialAccepts tm pref C j (A ∘ initialQuery j) = true
      apply (initialAccepts_all_iff tm pref C (by omega) A).mpr _ j
      rw [he]
      exact initial_real tm pref cert C S hc (by omega)
    · change stepAccepts tm.m j (A ∘ stepQuery t j) = true
      apply (stepAccepts_all_iff tm.m A t).mpr _ j
      rw [he,he]
      change Follows tm.m (Window.ofCfg S ((cfgNext tm.m)^[t.val] c))
        (Window.ofCfg S ((cfgNext tm.m)^[t.val+1] c))
      rw [Function.iterate_succ_apply']
      apply window_follows tm.m _ (pref.length+C+t.val*programRadius tm.m) S
        (cfgRun_length tm.m c (pref.length+C) t.val hb)
      have ht : t.val+1 ≤ H := t.isLt
      have hm := Nat.mul_le_mul_right (programRadius tm.m) ht
      simp only [Nat.add_mul,Nat.one_mul] at hm
      omega
    · cases u
      change decide ((A (Fin.last H,cellAddress S 0)).2 tm.k₁ = some out) = true
      rw [decide_eq_true_eq]
      simpa [A,tr,c,cellAddress,hpos,windowRow,Window.ofCfg] using hout

end DirectedFeedback.CookLevin

namespace DirectedFeedback.CookLevin
open Turing
attribute [local instance] FinTM2.ΛFin

theorem natPoly_mono (p : Polynomial ℕ) {n m : ℕ} (h : n ≤ m) : p.eval n ≤ p.eval m := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial k a => simpa only [Polynomial.eval_monomial] using
      Nat.mul_le_mul_left a (Nat.pow_le_pow_left h k)

namespace NPTableau

def certBound (V : NPVerifier) (n : ℕ) : ℕ := V.witnessBound.eval n
def inputBound (V : NPVerifier) (n : ℕ) : ℕ := 2*n+certBound V n+1
def horizon (V : NPVerifier) (n : ℕ) : ℕ := V.computation.time.eval (inputBound V n)
noncomputable def capacity (V : NPVerifier) (n : ℕ) : ℕ :=
  inputBound V n + horizon V n * programRadius V.computation.tm.m

def fixedPrefix (V : NPVerifier) (input : List Bool) : List (V.computation.tm.Γ V.computation.tm.k₀) :=
  (natBits input.length ++ input).map V.computation.inputAlphabet.invFun

theorem fixedPrefix_length (V : NPVerifier) (input : List Bool) :
    (fixedPrefix V input).length = 2*input.length+1 := by simp [fixedPrefix,natBits]; omega

def machine (V : NPVerifier) := V.computation.tm

noncomputable def tests (V : NPVerifier) (input : List Bool) :=
  tableau V.computation.tm (fixedPrefix V input) (certBound V input.length)
    (horizon V input.length) (capacity V input.length) (V.computation.outputAlphabet.invFun true)

theorem input_length_bound (V : NPVerifier) (input cert : List Bool)
    (hc : cert.length ≤ certBound V input.length) :
    (pairBits (input,cert)).length ≤ inputBound V input.length := by
  simp only [pairBits,natBits,List.length_append,List.length_replicate,List.length_singleton]
  unfold inputBound
  omega

theorem run_horizon (V : NPVerifier) (input : List Bool)
    (cert : List (V.computation.tm.Γ V.computation.tm.k₀))
    (hc : cert.length ≤ certBound V input.length) :
    ((cfgNext V.computation.tm.m)^[horizon V input.length]
      (initList V.computation.tm (fixedPrefix V input ++ cert))) =
    haltList V.computation.tm
      [V.computation.outputAlphabet.invFun (V.verify (input,cert.map V.computation.inputAlphabet))] := by
  let b := cert.map V.computation.inputAlphabet
  have hlen : b.length ≤ certBound V input.length := by simpa [b] using hc
  have hout := V.computation.outputsFun (input,b)
  have hmono := natPoly_mono V.computation.time (input_length_bound V input b hlen)
  have hr := output_run V.computation.tm
    ((pairBits (input,b)).map V.computation.inputAlphabet.invFun)
    (([V.verify (input,b)]).map V.computation.outputAlphabet.invFun)
    (horizon V input.length) ⟨hout.toEvalsTo,hout.steps_le_m.trans hmono⟩
  simpa [pairBits,fixedPrefix,b,List.map_append,List.map_map,Function.comp_def] using hr

theorem tests_satisfiable_iff (V : NPVerifier) (input : List Bool) :
    (tests V input).Satisfiable ↔ V.Accepts input := by
  have hsize : (fixedPrefix V input).length + certBound V input.length +
      horizon V input.length * programRadius V.computation.tm.m ≤ capacity V input.length := by
    rw [fixedPrefix_length]
    unfold capacity inputBound
    omega
  have hpos : 0 < capacity V input.length := by unfold capacity inputBound; omega
  rw [tests,tableau_satisfiable_iff _ _ _ _ _ hsize hpos]
  constructor
  · rintro ⟨cert,hc,hout⟩
    refine ⟨cert.map V.computation.inputAlphabet,by simpa only [List.length_map,certBound] using hc,?_⟩
    rw [run_horizon V input cert hc] at hout
    have he : V.computation.outputAlphabet.invFun (V.verify (input,cert.map V.computation.inputAlphabet)) =
        V.computation.outputAlphabet.invFun true := by
      simpa [haltList] using hout
    exact V.computation.outputAlphabet.symm.injective he
  · rintro ⟨cert,hc,htrue⟩
    let scert := cert.map V.computation.inputAlphabet.invFun
    have hsc : scert.length ≤ certBound V input.length := by simpa [scert,certBound] using hc
    refine ⟨scert,hsc,?_⟩
    rw [run_horizon V input scert hsc]
    simp [haltList,scert,List.map_map,Function.comp_def,htrue]

theorem atom_finite (V : NPVerifier) : Finite (Atom V.computation.tm.Γ
    V.computation.tm.Λ V.computation.tm.σ) := by
  let tm := V.computation.tm
  let _ : Fintype tm.K := tm.kFin
  let _ : Fintype tm.Λ := tm.ΛFin
  let _ : Fintype tm.σ := tm.σFin
  have : ∀ k, Finite (tm.Γ k) := V.finiteAlphabet
  change Finite (Atom tm.Γ tm.Λ tm.σ)
  infer_instance

theorem atom_nonempty (V : NPVerifier) : Nonempty (Atom V.computation.tm.Γ
    V.computation.tm.Λ V.computation.tm.σ) :=
  ⟨((none,V.computation.tm.initialState),fun _ => none)⟩

end NPTableau
end DirectedFeedback.CookLevin

end

end OAI
