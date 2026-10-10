import OAI.Computability.SpaceSimulation.OneTape.Single
import OAI.Computability.SpaceSimulation.Register.Digits

namespace OAI

namespace Fifths

namespace Entry
noncomputable def code {A : Type} [Fintype A] (a : A) : ℕ :=
  (Fintype.equivFin A a).val

theorem code_lt {A : Type} [Fintype A] (a : A) : code a < Fintype.card A :=
  (Fintype.equivFin A a).isLt

theorem code_inj (A : Type) [Fintype A] :
    Function.Injective (code (A := A)) :=
  Fin.val_injective.comp (Fintype.equivFin A).injective

noncomputable def parse (A : Type) [Fintype A] [Nonempty A] (k : ℕ) : A :=
  (Fintype.equivFin A).symm
    ⟨k % Fintype.card A,Nat.mod_lt _ Fintype.card_pos⟩

theorem code_parse (A : Type) [Fintype A] [Nonempty A] (k : ℕ) :
    code (parse A k) = k % Fintype.card A := by simp [code,parse]
@[simp] theorem parse_code {A : Type} [Fintype A] [Nonempty A] (x : A) :
    parse A (code x) = x := by
  apply code_inj A
  rw [code_parse,Nat.mod_eq_of_lt (code_lt x)]
end Entry

/-- Shifted by T into natural-address range; then the block partition
can be computed with unsigned arithmetic. -/
abbrev Square (T : ℕ) := Fin (2*T+1)

namespace Square
def cut (n a : ℕ) : Fin (n+1) := ⟨min n a,Nat.lt_succ_of_le (min_le_left _ _)⟩
@[simp] theorem cut_ok (n a : ℕ) (h : a≤n) : (cut n a).val = a := min_eq_right h
def atDisp (T : ℕ) (q : ℤ) : Square T := cut (2*T) (q+T).toNat
def disp {T : ℕ} (s : Square T) : ℤ := (s.val:ℤ) - T

theorem bounded {T} (s : Square T) : Single.Inside T (disp s) := by
  have h := s.isLt
  unfold Single.Inside disp; omega
theorem disp_at {T : ℕ} (q : ℤ) (h : Single.Inside T q) :
    disp (atDisp T q) = q := by
  unfold Single.Inside at h
  unfold disp atDisp
  rw [cut_ok]
  · omega
  · omega
theorem disp_inj (T : ℕ) : Function.Injective (disp (T:=T)) := by
  intro a b h; unfold disp at h; apply Fin.ext; omega
theorem at_disp {T : ℕ} (s : Square T) : atDisp T (disp s) = s :=
  disp_inj T (disp_at _ (bounded s))

def adjacent {T : ℕ} (s : Square T) (d : Dir) : Square T :=
  match d with
  | .L => cut (2*T) (s.val-1)
  | .R => cut (2*T) (s.val+1)
  | .N => s
theorem adj {T} (s : Square T) (d : Dir)
    (h : Single.Inside T (disp s + d.delta)) :
    adjacent s d = atDisp T (disp s + d.delta) := by
  apply disp_inj T
  rw [disp_at _ h]
  have v := s.isLt
  unfold Single.Inside disp at h
  unfold disp
  cases d
  · simp only [adjacent,Dir.delta] at *
    rw [cut_ok] <;> omega
  · simp [adjacent]
  · simp only [adjacent,Dir.delta] at *
    rw [cut_ok] <;> omega
end Square

structure Site where
  T : ℕ
  k : ℕ
  positive : 0 < k
  left : Fin (k*k) -- offset to add

namespace Site
open Square
variable (W : Site)

def b := W.k*W.k
theorem b_pos : 0 < W.b := Nat.mul_pos W.positive W.positive
def N := 2*W.T + W.b + 2
def home (s : Square W.T) := (W.left.val+s.val)/W.b
def slot (s : Square W.T) := (W.left.val+s.val)%W.b

theorem home_lt (s : Square W.T) : W.home s < W.N := by
  have a := s.isLt
  have h : W.left.val < W.b := W.left.isLt
  have p := Nat.div_le_self (W.left.val+s.val) W.b
  unfold home N
  omega
theorem slot_lt (s : Square W.T) : W.slot s < W.b := Nat.mod_lt _ W.b_pos

def reach (i j : ℕ) : Bool :=
  decide (W.left.val ≤ i*W.b+j ∧ i*W.b+j ≤ W.left.val+2*W.T)
def pin (i j : ℕ) : Square W.T := cut (2*W.T) ((i*W.b+j)-W.left.val)

theorem packed_index (s : Square W.T) : W.home s*W.b + W.slot s = W.left.val+s.val := by
  unfold home slot
  rw [mul_comm,add_comm,Nat.mod_add_div]
theorem pin_ok (s : Square W.T) :
    W.reach (W.home s) (W.slot s) = true ∧ W.pin (W.home s) (W.slot s) = s := by
  have a := s.isLt
  unfold reach pin
  rw [W.packed_index]
  constructor
  · apply decide_eq_true; omega
  · apply Fin.ext
    rw [cut_ok] <;> omega

theorem backwards (i j : ℕ) (l : j<W.b) (p : W.reach i j = true) :
    W.home (W.pin i j) = i ∧ W.slot (W.pin i j) = j := by
  unfold reach at p
  have o := of_decide_eq_true p
  unfold home slot pin; rw [cut_ok _ _ (by omega)]
  rw [show W.left.val + (i*W.b+j-W.left.val) = j+W.b*i by
    rw [mul_comm W.b]; omega]
  simp [Nat.add_mul_div_left, W.b_pos,Nat.mod_eq_of_lt l,l]
end Site

namespace Single
open Square Entry Radix
variable {X : Type} (M : Single X)

/-- Field of a controller is w(T) bits. Pad cell entries even further,
to match a controller as a whole, for one consistent block radix. -/
def w (T : ℕ) := (2*T + Fintype.card M.Q + Fintype.card M.A + 1).size
def q (T : ℕ) := 2 ^ M.w T
def fields := M.heads+3
def c (T : ℕ) := M.w T * M.fields
def radix (T : ℕ) := 2 ^ M.c T

theorem qpos (T) : 0 < M.q T := by unfold q; positivity
theorem short (T) :
    2*T < M.q T ∧ Fintype.card M.Q ≤ M.q T ∧ Fintype.card M.A ≤ M.q T := by
  unfold q w
  have := Nat.lt_size_self (2*T + Fintype.card M.Q + Fintype.card M.A + 1)
  omega
theorem powers (T) : M.q T ^ M.fields = M.radix T := by
  unfold q radix c; rw [← pow_mul]

theorem rpos (T) : 0 < M.radix T := by unfold radix; positivity
theorem moduli (T) : M.q T ≤ M.radix T := calc
  _ = M.q T ^ 1 := by simp
  _ ≤ M.q T ^ M.fields := Nat.pow_le_pow_right (M.qpos _) (by unfold fields; omega)
  _ = _ := M.powers _

structure Control (T : ℕ) where
  tick : Fin (T+1)
  state : M.Q
  now : Square T
  other : Fin M.heads → Square T

noncomputable def key {T} (c : M.Control T) (i : ℕ) : ℕ :=
  if i=0 then c.tick.val else if i=1 then code c.state else if i=2 then c.now.val
  else if p : i-3 < M.heads then (c.other ⟨i-3,p⟩).val else 0

noncomputable def packCtrl {T} (c : M.Control T) := pack (M.q T) (M.key c) M.fields

noncomputable def parseCtrl (T : ℕ) (z : ℕ) : M.Control T := ⟨cut T (get (M.q T) z 0),
  parse M.Q (get (M.q T) z 1), cut (2*T) (get (M.q T) z 2),
  fun j => cut (2*T) (get (M.q T) z (j.val+3))⟩
theorem key_lt {T} (c : M.Control T) (i) : M.key c i < M.q T := by
  have a := c.now.isLt
  have b := c.tick.isLt
  obtain ⟨h,l,o⟩ := M.short T
  unfold key; split_ifs with _ _ _ p
  · omega
  · exact lt_of_lt_of_le (code_lt _) l
  · omega
  · have := (c.other ⟨_,p⟩).isLt; omega
  · omega
theorem packed_short {T} (c : M.Control T) : M.packCtrl c < M.radix T :=
  lt_of_lt_of_le (pack_lt (M.qpos _) _ _ (fun i _ => M.key_lt c i)) (M.powers T).le

theorem roundtrip {T} (c : M.Control T) : M.parseCtrl T (M.packCtrl c) = c := by
  have e (i : ℕ) (p : i < M.heads+3) :
      get (M.q T) (M.packCtrl c) i = M.key c i :=
    get_pack (M.qpos _) _ _ (fun i _ => M.key_lt c i) p
  have h (n) (p : Fin (n+1)) : cut n p.val = p :=
    Fin.ext (cut_ok _ _ (by have := p.isLt; omega))
  unfold parseCtrl
  rw [e 0 (by omega),e 1 (by omega),e 2 (by omega)]
  have g : (fun j : Fin M.heads => cut (2*T) (get (M.q T) (M.packCtrl c) (j.val+3))) =
      c.other := by
    funext j; have p := j.isLt
    rw [e _ (by omega)]
    simp [key,p,h] -- small index tests
  rw [g]
  simp [key,h]
end Single
end Fifths

end OAI
