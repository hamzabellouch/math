import OAI.Computability.SpaceSimulation.OneTape.Layout
import OAI.Computability.SpaceSimulation.Epoch.Core

namespace OAI

/-!
Local/global correspondence for a visit. Work in addresses
[0,2T]. Arithmetic for neighboring positions saturates on raw calls,
though it won't clamp an in-budget move on the represented trajectory.
Run locally through the cap when halted too (advancing only tick).
-/
namespace Fifths.Single
open Radix Square Entry
variable {X : Type} (M : Single X)

def capture (T : ℕ) (n : ℕ) (s : M.At) : M.Control T :=
  ⟨cut T n,s.state,atDisp T s.tape.pos,fun j => atDisp T (s.ro j)⟩

noncomputable def glimpse (W : Site) (l : ℤ → M.A) (i j : ℕ) : ℕ :=
  code (if W.reach i j then l (disp (W.pin i j)) else Entry.parse M.A 0)
noncomputable def stored (W : Site) (l : ℤ → M.A) (i : ℕ) :=
  pack (M.radix W.T) (fun j => M.glimpse W l i j) W.b

noncomputable def view (x : List X) (W : Site) (n : ℕ) : Scene :=
  let s := M.atTime x n
  ⟨M.packCtrl (M.capture W.T n s), M.stored W s.tape.sym⟩

noncomputable def refresh (W : Site) (B j : ℕ) (a : M.A) :=
  pack (M.radix W.T) (fun i => if i=j then code a else get (M.radix W.T) B i) W.b

noncomputable def localTable (x : List X) (W : Site) (c : M.Control W.T) (B : ℕ) :=
  M.move c.state
    (parse M.A (get (M.radix W.T) B (W.slot c.now)))
    (fun j => M.sensor x (some j) (disp (c.other j)))
def traceCtrl {T} (c : M.Control T) (a : SingleAct M.Q M.A M.heads) :
    M.Control T :=
  ⟨cut T (c.tick.val+1), a.out, adjacent c.now a.write.dir,
   fun j => adjacent (c.other j) (a.others j)⟩

noncomputable def localStep (x : List X) (W : Site) (i : ℕ) (s : ℕ × ℕ) :
    ℕ × ℕ :=
  let c := M.parseCtrl W.T s.1
  let a := M.localTable x W c s.2
  if c.tick.val < W.T ∧ W.home c.now = i then
    (M.packCtrl (M.traceCtrl c a),M.refresh W s.2 (W.slot c.now) a.write.sym)
  else s

noncomputable def chooseBlock (W : Site) (z : ℕ) :=
  W.home (M.parseCtrl W.T z).now

noncomputable def sweep (M : Single X) (x : List X) (W : Site) (z B : ℕ) :
    ℕ → ℕ × ℕ
  | 0 => (z,B)
  | n+1 => M.localStep x W (M.chooseBlock W z) (M.sweep x W z B n)
noncomputable def tour (x : List X) (W : Site) : Tour where
  k := W.k
  c := M.c W.T
  N := W.N
  pk := W.positive
  blocks := by unfold Site.N; omega
  init := (M.view x W 0).ctrl
  tape := (M.view x W 0).cells
  sel := M.chooseBlock W
  rangeSel z := W.home_lt _
  visit := fun z b => M.sweep x W z b W.T

theorem sym_lt (T : ℕ) (s : M.A) : Entry.code s < M.radix T :=
  lt_of_lt_of_le (Entry.code_lt s) ((M.short T).2.2.trans (M.moduli T))
theorem stored_lt (W : Site) (s : ℤ → M.A) (i : ℕ) :
    M.stored W s i < M.radix W.T ^ W.b :=
  pack_lt (M.rpos _) _ _ (fun _ _ => M.sym_lt _ _)
theorem refresh_lt (W : Site) (s i) (a : M.A) :
    M.refresh W s i a < M.radix W.T ^ W.b := by
  apply pack_lt (M.rpos _)
  intro j _
  split
  · exact M.sym_lt _ a
  · exact get_lt (M.rpos _) _ _

theorem sweep_bounded (W : Site) (x : List X) (z B : ℕ) (n)
    (l : z<M.radix W.T) (p : B<M.radix W.T^W.b) :
    (M.sweep x W z B n).1 < M.radix W.T ∧ (M.sweep x W z B n).2 < M.radix W.T^W.b := by
  induction n with
  | zero => exact ⟨l,p⟩
  | succ n ih =>
    simp only [sweep,localStep]
    split
    · exact ⟨M.packed_short _,M.refresh_lt ..⟩
    · exact ih

theorem tour_bounded (x : List X) (W : Site) :
    (M.tour x W).FiniteWords :=
  ⟨M.packed_short _,fun i => M.stored_lt _ _ i,fun z B => M.sweep_bounded W x z B W.T⟩

-- Write correctness
theorem rep_sym (W : Site) (f : ℤ → M.A) (p : Square W.T) :
    get (M.radix W.T) (M.stored W f (W.home p)) (W.slot p) =
      code (f (disp p)) := by
  rw [stored,get_pack (M.rpos _) (fun j => M.glimpse W f (W.home p) j) _ (fun _ _ => M.sym_lt _ _) (W.slot_lt p)]
  simp [glimpse,(W.pin_ok p).1,(W.pin_ok p).2]

theorem rep_write (W : Site) (f : ℤ → M.A) (p : Square W.T) (s : M.A) (i : ℕ) :
    M.stored W (Function.update f (disp p) s) i =
      if W.home p = i then M.refresh W (M.stored W f i) (W.slot p) s
      else M.stored W f i := by
  classical
  have e (j l : ℕ) (h : l < W.b) (o : W.reach j l = true)
      (u : disp (W.pin j l) = disp p) :
      W.home p = j ∧ W.slot p = l := by
    rw [← Square.disp_inj W.T u]
    exact W.backwards j l h o
  split
  next h =>
    subst i
    apply pack_congr
    intro l g
    by_cases b : l = W.slot p
    · subst l
      simp [glimpse, (W.pin_ok p).1, (W.pin_ok p).2]
    · simp only [stored,b,↓reduceIte,get_pack (M.rpos _) (fun j => M.glimpse W f (W.home p) j) _
        (fun _ _ => M.sym_lt _ _) g]
      unfold glimpse
      split <;> rename_i a
      · rw [Function.update_of_ne (fun u => b (e _ _ g a u).2.symm)]
      · rfl
  next q =>
    apply pack_congr
    intro l g
    unfold glimpse
    split <;> rename_i b
    · rw [Function.update_of_ne (fun u => q (e i l g b u).1)]
    · rfl

def seenPos (x : List X) (T n : ℕ) : Square T :=
  atDisp T (M.atTime x n).tape.pos
def place (x : List X) (W : Site) (n : ℕ) :=
  W.home (M.seenPos x W.T n)
theorem so_select (x : List X) (W : Site) (n) :
    M.chooseBlock W (M.view x W n).ctrl = M.place x W n := by
  simp [chooseBlock,view,M.roundtrip,place,capture,seenPos]
theorem seenBack (x : List X) {n T : ℕ} (h : n ≤ T) :
    disp (M.seenPos x T n) = (M.atTime x n).tape.pos := by
  apply disp_at
  have g := (M.nearby x n).1
  unfold Inside at *
  omega

/-- Single capped step from the representation, selected block in
work space. -/
theorem realize (x : List X) (W : Site) (n i : ℕ) (l : n < W.T)
    (h : M.place x W n = i) :
    M.localStep x W i ((M.view x W n).ctrl,(M.view x W n).cells i) =
       ((M.view x W (n+1)).ctrl,(M.view x W (n+1)).cells i)
    ∧ ∀ j, j ≠ i → (M.view x W n).cells j = (M.view x W (n+1)).cells j := by
  subst i
  let v := M.atTime x n
  let u := M.seenPos x W.T n
  let c := M.capture W.T n v
  let a := M.move v.state v.tape.see (fun j => M.sensor x (some j) (v.ro j))
  let d := M.atTime x (n+1)
  have p : disp u = v.tape.pos := M.seenBack x l.le
  have e : M.localTable x W c ((M.view x W n).cells (M.place x W n)) = a := by
    have q : ∀ j, disp (c.other j) = v.ro j := by
      intro j; apply disp_at
      have y := (M.nearby x n).2 j
      change Inside n _ at y
      dsimp [v]; unfold Inside at *; omega
    change M.move v.state
      (Entry.parse _ (get _ (M.stored W v.tape.sym (W.home u)) (W.slot u)))
      (fun j => M.sensor x (some j) (disp (c.other j))) = _
    simp only [M.rep_sym,Entry.parse_code,q,p]
    rfl
  have ct : c.tick.val = n := cut_ok _ _ l.le
  have v' : M.traceCtrl c a = M.capture W.T (n+1) d := by
    have q : ∀ j, disp (c.other j) = v.ro j := by
      intro j; apply disp_at
      have y := (M.nearby x n).2 j
      dsimp [v]; unfold Inside at *; omega
    have b : adjacent c.now a.write.dir = atDisp W.T d.tape.pos := by
      change adjacent u _ = atDisp W.T _
      rw [adj]
      · rw [p]; rfl
      rw [p]
      change Inside W.T d.tape.pos
      have y := (M.nearby x (n+1)).1
      dsimp [d]; unfold Inside at *; omega
    have g : ∀ j, adjacent (c.other j) (a.others j) = atDisp W.T (d.ro j) := by
      intro j; rw [adj]
      · rw [q]; rfl
      rw [q]
      change Inside W.T (d.ro j)
      have y := (M.nearby x (n+1)).2 j
      dsimp [d]; unfold Inside at *; omega
    simp only [traceCtrl,capture,b,g,ct]
    rfl
  have y (j : ℕ) :
      (M.view x W (n+1)).cells j = if M.place x W n = j then
        M.refresh W ((M.view x W n).cells j) (W.slot c.now) a.write.sym
        else (M.view x W n).cells j := by
    have g := M.rep_write W v.tape.sym u a.write.sym j
    rw [p] at g
    exact g
  constructor
  · have g : M.parseCtrl W.T (M.view x W n).ctrl = c := M.roundtrip c
    dsimp only [localStep]
    rw [g,e,ite_eq_left (And.intro (ct.trans_lt l) (show W.home c.now = M.place x W n from rfl)),y,ite_eq_left rfl,v']
    rfl
  intro j g
  rw [y,ite_eq_right g.symm]
end Fifths.Single

end OAI
