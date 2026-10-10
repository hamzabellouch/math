import Mathlib
import OAI.GroupTheory.PeriodicGroups.Steinberg.PresentationModel

namespace OAI

section
universe u v w
namespace SourceBurnside

theorem one_add_nilpotent_periodic {A : Type u} [Ring A] [CharP A 2]
    {a : A} (ha : IsNilpotent a) : ∃ m : ℕ, 0 < m ∧ (1 + a) ^ m = 1 := by
  obtain ⟨r, hr⟩ := ha
  refine ⟨2 ^ r, pow_pos (by decide) _, ?_⟩
  rw [add_pow_char_pow_of_commute 2 r (Commute.one_left a), one_pow,
    pow_eq_zero_of_le (Nat.le_of_lt r.lt_two_pow_self) hr, add_zero]

def MatrixNilKernel {R : Type u} [Ring R] (ε : R →+* ZMod 2) : Prop :=
  ∀ n (A : Matrix (Fin n) (Fin n) R),
    (∀ i j, ε (A i j) = 0) → IsNilpotent A

theorem matrix_units_periodic {R : Type u} [Ring R] [CharP R 2]
    (ε : R →+* ZMod 2) (hI : MatrixNilKernel ε) (n : ℕ) :
    Periodic (Matrix (Fin n) (Fin n) R)ˣ := by
  classical
  cases n with
  | zero =>
    intro g
    exact ⟨1, by decide, Subsingleton.elim _ _⟩
  | succ n =>
    intro g
    let f : (Matrix (Fin (n + 1)) (Fin (n + 1)) R)ˣ →* (Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2))ˣ :=
      Units.map ε.mapMatrix.toMonoidHom
    let d := Fintype.card (Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2))ˣ
    have hd : 0 < d := Fintype.card_pos
    have hred : f (g ^ d) = 1 := by rw [map_pow]; exact pow_card_eq_one
    have hnil : IsNilpotent ((↑(g ^ d) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1) := by
      apply hI (n + 1)
      intro i j
      have he := congrArg (fun u : (Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2))ˣ => u.val i j) hred
      have hm : ε.mapMatrix (↑(g ^ d) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) = 1 :=
        congrArg Units.val hred
      have he' := congrArg (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) => A i j)
        (show ε.mapMatrix ((↑(g ^ d) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1) = 0 by
          rw [map_sub, hm, map_one, sub_self])
      exact he'
    obtain ⟨m, hm, hpow⟩ := one_add_nilpotent_periodic hnil
    refine ⟨d * m, Nat.mul_pos hd hm, ?_⟩
    apply Units.ext
    rw [pow_mul, Units.val_pow_eq_pow_val]
    have hh : (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) + (↑(g ^ d) - 1) = ↑(g ^ d) := by abel
    rw [hh] at hpow
    exact hpow

theorem periodic_of_image_and_kernel {G : Type u} {H : Type v} [Group G] [Group H]
    (f : G →* H) (hH : Periodic H)
    (hK : ∀ g : G, f g = 1 → ∃ r : ℕ, 0 < r ∧ g ^ r = 1) : Periodic G := by
  intro g
  obtain ⟨m, hm, hp⟩ := hH (f g)
  obtain ⟨r, hr, hq⟩ := hK (g ^ m) (by simpa using hp)
  exact ⟨m * r, Nat.mul_pos hm hr, by simpa only [pow_mul] using hq⟩

namespace CommutatorCalculus

variable {G : Type u} [Group G]

 theorem commute_bracket_right {x a b : G} (ha : Commute x a) (hb : Commute x b) :
    Commute x (bracket a b) :=
  ((ha.mul_right hb).mul_right ha.inv_right).mul_right hb.inv_right

 theorem commute_bracket_left {a b x : G} (ha : Commute a x) (hb : Commute b x) :
    Commute (bracket a b) x := (commute_bracket_right ha.symm hb.symm).symm

 theorem mul_left (a b c : G) :
    bracket (a * b) c = a * bracket b c * a⁻¹ * bracket a c := by
  simp [bracket, mul_assoc]

 theorem mul_right (a b c : G) :
    bracket a (b * c) = bracket a b * b * bracket a c * b⁻¹ := by
  simp [bracket, mul_assoc]

 theorem conj_of_commute {a b : G} (h : Commute a b) : a * b * a⁻¹ = b := by
  rw [h.eq, mul_inv_cancel_right]

 theorem separated (a b c d : G)
    (hac : Commute a c) (had : Commute a d)
    (hbc : Commute b c) (hbd : Commute b d) :
    bracket (a * c) (b * d) = bracket a b * bracket c d := by
  have hAD := commute_bracket_right hac had
  have hBD := commute_bracket_right hbc hbd
  rw [mul_left, mul_right, mul_right,
    (bracket_eq_one_iff _ _).mpr hbc.symm,
    (bracket_eq_one_iff _ _).mpr had]
  simp only [one_mul, mul_one, mul_inv_cancel_right]
  rw [conj_of_commute hBD, conj_of_commute hAD]
  exact (commute_bracket_left hAD hBD).symm.eq

 theorem three_factor (X Y Z : G)
    (hAX : Commute (bracket X Y) X) (_hAY : Commute (bracket X Y) Y)
    (_hBY : Commute (bracket Y Z) Y) (hBZ : Commute (bracket Y Z) Z)
    (hAB : Commute (bracket X Y) (bracket Y Z)) (hXZ : Commute X Z) :
    bracket (bracket X Y) Z = bracket X (bracket Y Z) ∧
    Commute (bracket (bracket X Y) Z) (bracket X Y) ∧
    Commute (bracket (bracket X Y) Z) Z ∧
    Commute (bracket (bracket X Y) Z) X ∧
    Commute (bracket (bracket X Y) Z) (bracket Y Z) := by
  let A := bracket X Y
  let B := bracket Y Z
  let C := bracket A⁻¹ Z
  let D := bracket X B
  have hconjX : Y * X * Y⁻¹ = A⁻¹ * X := by simp [A, bracket, mul_assoc]
  have hconjZ : Y * Z * Y⁻¹ = B * Z := by simp [B, bracket, mul_assoc]
  have hc : Commute (A⁻¹ * X) (Z * B) := by
    have hBZeq : B * Z = Z * B := hBZ.eq
    simpa only [hconjX, hconjZ, hBZeq] using hXZ.conj Y
  have hCD : C * D = 1 := by
    rw [← separated A⁻¹ Z X B hAX.inv_left hAB.inv_left hXZ.symm hBZ.symm]
    exact (bracket_eq_one_iff _ _).mpr hc
  have hC : C = D⁻¹ := eq_inv_of_mul_eq_one_left hCD
  have hDA : Commute D A := commute_bracket_left hAX.symm hAB.symm
  have hDZ : Commute D Z := commute_bracket_left hXZ hBZ
  have hCX : Commute C X := commute_bracket_left hAX.inv_left hXZ.symm
  have hCB : Commute C B := commute_bracket_left hAB.inv_left hBZ.symm
  have hCA : Commute C A := hC ▸ hDA.inv_left
  have hmain : bracket A Z = D := by
    apply inv_injective
    calc
      (bracket A Z)⁻¹ = A * C * A⁻¹ := by simp [C, bracket, mul_assoc]
      _ = C := conj_of_commute hCA.symm
      _ = D⁻¹ := hC
  refine ⟨hmain, ?_, ?_, ?_, ?_⟩
  · exact hmain ▸ hDA
  · exact hmain ▸ hDZ
  · rw [hmain]
    exact (Commute.inv_left_iff.mp (hC ▸ hCX))
  · rw [hmain]
    exact (Commute.inv_left_iff.mp (hC ▸ hCB))

end CommutatorCalculus

theorem exists_fresh {n : ℕ} (hn : 5 ≤ n) (i j k l : Fin n) :
    ∃ a : Fin n, a ≠ i ∧ a ≠ j ∧ a ≠ k ∧ a ≠ l := by
  have hcard : ({i, j, k, l} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    have := (Finset.card_le_four : ({i, j, k, l} : Finset (Fin n)).card ≤ 4)
    simpa using (lt_of_le_of_lt this (show 4 < n by omega))
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨a, by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using ha⟩

namespace MonomialCompletion

variable {n : ℕ} {α : Type u} {G : Type v} [Group G]

structure Seed (n : ℕ) (α : Type u) (G : Type v) [Group G] where
  g : Root n → List α → G
  square : ∀ p w, w.length ≤ 2 → g p w ^ 2 = 1
  commute : ∀ p q u v, u.length ≤ 2 → v.length ≤ 2 →
    p.col ≠ q.row → p.row ≠ q.col → Commute (g p u) (g q v)
  product : ∀ (i j k : Fin n) hij hjk hik (u v : List α),
    u.length + v.length ≤ 2 →
    bracket (g ⟨i, j, hij⟩ u) (g ⟨j, k, hjk⟩ v) = g ⟨i, k, hik⟩ (u ++ v)

noncomputable def middle (hn : 5 ≤ n) (p : Root n) : Fin n :=
  (exists_fresh hn p.row p.col p.row p.col).choose

theorem middle_ne_row (hn : 5 ≤ n) (p : Root n) : middle hn p ≠ p.row :=
  (exists_fresh hn p.row p.col p.row p.col).choose_spec.1

theorem middle_ne_col (hn : 5 ≤ n) (p : Root n) : middle hn p ≠ p.col :=
  (exists_fresh hn p.row p.col p.row p.col).choose_spec.2.1

noncomputable def word (s : Seed n α G) (hn : 5 ≤ n) (p : Root n) : List α → G
  | [] => s.g p []
  | [a] => s.g p [a]
  | [a, b] => s.g p [a, b]
  | a :: b :: c :: w =>
    bracket (s.g ⟨p.row, middle hn p, (middle_ne_row hn p).symm⟩ [a])
      (word s hn ⟨middle hn p, p.col, middle_ne_col hn p⟩ (b :: c :: w))

 theorem word_short (s : Seed n α G) (hn : 5 ≤ n) (p : Root n) (w : List α)
    (hw : w.length ≤ 2) : word s hn p w = s.g p w := by
  match w with
  | [] | [_] | [_, _] => rfl
  | _ :: _ :: _ :: _ => simp only [List.length_cons] at hw; omega

 theorem word_long (s : Seed n α G) (hn : 5 ≤ n) (p : Root n) (a : α) (v : List α)
    (hv : 2 ≤ v.length) :
    word s hn p (a :: v) =
      bracket (word s hn ⟨p.row, middle hn p, (middle_ne_row hn p).symm⟩ [a])
        (word s hn ⟨middle hn p, p.col, middle_ne_col hn p⟩ v) := by
  match v with
  | [] | [_] => simp only [List.length_cons, List.length_nil] at hv; omega
  | _ :: _ :: _ => rfl

abbrev RootWords (n : ℕ) (α : Type u) (G : Type v) := Root n → List α → G

def ProductUpTo (y : RootWords n α G) (N : ℕ) : Prop :=
  ∀ (i j k : Fin n) hij hjk hik (u v : List α), u.length + v.length ≤ N →
    bracket (y ⟨i, j, hij⟩ u) (y ⟨j, k, hjk⟩ v) = y ⟨i, k, hik⟩ (u ++ v)

def CommuteUpTo (y : RootWords n α G) (N : ℕ) : Prop :=
  ∀ p q u v, u.length ≤ N → v.length ≤ N → p.col ≠ q.row → p.row ≠ q.col →
    Commute (y p u) (y q v)

def SquaresUpTo (y : RootWords n α G) (N : ℕ) : Prop :=
  ∀ p w, w.length ≤ N → y p w ^ 2 = 1

def Good (y : RootWords n α G) (N : ℕ) : Prop :=
  ProductUpTo y N ∧ CommuteUpTo y N ∧ SquaresUpTo y N

 theorem base_good (s : Seed n α G) (hn : 5 ≤ n) (N : ℕ) (hN : N ≤ 2) :
    Good (word s hn) N := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j k hij hjk hik u v huv
    rw [word_short _ _ _ _ (by omega), word_short _ _ _ _ (by omega),
      word_short _ _ _ _ (by simp only [List.length_append]; omega)]
    exact s.product i j k hij hjk hik u v (by omega)
  · intro p q u v hu hv h₁ h₂
    rw [word_short _ _ _ _ (by omega), word_short _ _ _ _ (by omega)]
    exact s.commute p q u v (by omega) (by omega) h₁ h₂
  · intro p w hw
    rw [word_short _ _ _ _ (by omega)]
    exact s.square p w (by omega)

 theorem reassociate_of (y : RootWords n α G) {M : ℕ}
    (hc : CommuteUpTo y M)
    (i a b j : Fin n) (hia : i ≠ a) (hib : i ≠ b) (hij : i ≠ j)
    (hab : a ≠ b) (haj : a ≠ j) (hbj : b ≠ j)
    (u v z : List α) (huv : u.length + v.length ≤ M) (hvz : v.length + z.length ≤ M)
    (hA : bracket (y ⟨i, a, hia⟩ u) (y ⟨a, b, hab⟩ v) = y ⟨i, b, hib⟩ (u ++ v))
    (hB : bracket (y ⟨a, b, hab⟩ v) (y ⟨b, j, hbj⟩ z) = y ⟨a, j, haj⟩ (v ++ z)) :
    bracket (y ⟨i, b, hib⟩ (u ++ v)) (y ⟨b, j, hbj⟩ z) =
      bracket (y ⟨i, a, hia⟩ u) (y ⟨a, j, haj⟩ (v ++ z)) := by
  have h := CommutatorCalculus.three_factor
    (y ⟨i, a, hia⟩ u) (y ⟨a, b, hab⟩ v) (y ⟨b, j, hbj⟩ z)
    (by rw [hA]; exact hc _ _ _ _ (by simp only [List.length_append]; omega) (by omega) hib.symm hia)
    (by rw [hA]; exact hc _ _ _ _ (by simp only [List.length_append]; omega) (by omega) hab.symm hib)
    (by rw [hB]; exact hc _ _ _ _ (by simp only [List.length_append]; omega) (by omega) haj.symm hab)
    (by rw [hB]; exact hc _ _ _ _ (by simp only [List.length_append]; omega) (by omega) hbj.symm haj)
    (by
      rw [hA, hB]
      exact hc _ _ _ _ (by simp only [List.length_append]; omega)
        (by simp only [List.length_append]; omega) hab.symm hij)
    (hc _ _ _ _ (by omega) (by omega) hab hij)
  simpa only [hA, hB] using h.1

 theorem reassociate (y : RootWords n α G) {M : ℕ}
    (hp : ProductUpTo y M) (hc : CommuteUpTo y M)
    (i a b j : Fin n) (hia : i ≠ a) (hib : i ≠ b) (hij : i ≠ j)
    (hab : a ≠ b) (haj : a ≠ j) (hbj : b ≠ j)
    (u v z : List α) (huv : u.length + v.length ≤ M) (hvz : v.length + z.length ≤ M) :
    bracket (y ⟨i, b, hib⟩ (u ++ v)) (y ⟨b, j, hbj⟩ z) =
      bracket (y ⟨i, a, hia⟩ u) (y ⟨a, j, haj⟩ (v ++ z)) :=
  reassociate_of y hc i a b j hia hib hij hab haj hbj u v z huv hvz
    (hp i a b hia hab hib u v huv) (hp a b j hab hbj haj v z hvz)

 theorem first_cut_independent (y : RootWords n α G) (hn : 5 ≤ n) {M : ℕ}
    (hp : ProductUpTo y M) (hc : CommuteUpTo y M)
    (i j h h' : Fin n) (hij : i ≠ j) (hih : i ≠ h) (hhj : h ≠ j)
    (hih' : i ≠ h') (hh'j : h' ≠ j) (a b : α) (v : List α)
    (hM : 2 ≤ M) (hv : 1 + v.length ≤ M) :
    bracket (y ⟨i, h, hih⟩ [a]) (y ⟨h, j, hhj⟩ (b :: v)) =
      bracket (y ⟨i, h', hih'⟩ [a]) (y ⟨h', j, hh'j⟩ (b :: v)) := by
  obtain ⟨c, hci, hcj, hch, hch'⟩ := exists_fresh hn i j h h'
  have h₁ := reassociate y hp hc i h c j hih hci.symm hij hch.symm hhj hcj
    [a] [b] v (by simpa) (by simpa [Nat.add_comm] using hv)
  have h₂ := reassociate y hp hc i h' c j hih' hci.symm hij hch'.symm hh'j hcj
    [a] [b] v (by simpa) (by simpa [Nat.add_comm] using hv)
  simpa using h₁.symm.trans h₂

 theorem first_cut_next (s : Seed n α G) (hn : 5 ≤ n) {M : ℕ}
    (hp : ProductUpTo (word s hn) M) (hc : CommuteUpTo (word s hn) M)
    (i h j : Fin n) (hih : i ≠ h) (hhj : h ≠ j) (hij : i ≠ j)
    (a : α) (v : List α) (hv₂ : 2 ≤ v.length) (hvM : v.length ≤ M) :
    bracket (word s hn ⟨i, h, hih⟩ [a]) (word s hn ⟨h, j, hhj⟩ v) =
      word s hn ⟨i, j, hij⟩ (a :: v) := by
  rw [word_long _ _ _ _ _ hv₂]
  cases v with
  | nil => simp at hv₂
  | cons b v =>
    exact first_cut_independent _ hn hp hc i j h (middle hn ⟨i, j, hij⟩)
      hij hih hhj (middle_ne_row hn ⟨i, j, hij⟩).symm (middle_ne_col hn ⟨i, j, hij⟩) a b v
      (by omega) (by simpa [Nat.add_comm] using hvM)

 theorem positive_next (s : Seed n α G) (hn : 5 ≤ n) {M : ℕ} (hM : 2 ≤ M)
    (hp : ProductUpTo (word s hn) M) (hc : CommuteUpTo (word s hn) M)
    (i h j : Fin n) (hih : i ≠ h) (hhj : h ≠ j) (hij : i ≠ j)
    (u v : List α) (hu : 0 < u.length) (hv : 0 < v.length)
    (huv : u.length + v.length ≤ M + 1) :
    bracket (word s hn ⟨i, h, hih⟩ u) (word s hn ⟨h, j, hhj⟩ v) =
      word s hn ⟨i, j, hij⟩ (u ++ v) := by
  by_cases hsmall : u.length + v.length ≤ M
  · exact hp i h j hih hhj hij u v hsmall
  cases u with
  | nil => simp at hu
  | cons a u =>
    cases u with
    | nil =>
      exact first_cut_next s hn hp hc i h j hih hhj hij a v
        (by simp only [List.length_cons, List.length_nil] at hsmall; omega)
        (by simp only [List.length_cons, List.length_nil] at huv; omega)
    | cons b u =>
      obtain ⟨c, hci, hcj, hch, _⟩ := exists_fresh hn i j h h
      have hassoc := reassociate (word s hn) hp hc i c h j hci.symm hih hij
        hch hcj hhj [a] (b :: u) v
        (by simp only [List.length_cons, List.length_nil] at *; omega)
        (by simp only [List.length_cons] at *; omega)
      calc
        bracket (word s hn ⟨i, h, hih⟩ (a :: b :: u)) (word s hn ⟨h, j, hhj⟩ v) =
            bracket (word s hn ⟨i, c, hci.symm⟩ [a])
              (word s hn ⟨c, j, hcj⟩ ((b :: u) ++ v)) := hassoc
        _ = word s hn ⟨i, j, hij⟩ ((a :: b :: u) ++ v) :=
          first_cut_next s hn hp hc i c j hci.symm hcj hij a ((b :: u) ++ v)
            (by simp only [List.length_cons, List.length_append] at *; omega)
            (by simp only [List.length_cons, List.length_append] at *; omega)

 theorem commute_next_short (s : Seed n α G) (hn : 5 ≤ n) {M : ℕ} (hM : 2 ≤ M)
    (hp : ProductUpTo (word s hn) M) (hc : CommuteUpTo (word s hn) M)
    (p q : Root n) (u v : List α) (hu : u.length ≤ M + 1) (hv : v.length ≤ M)
    (hpq : p.col ≠ q.row) (hqp : p.row ≠ q.col) :
    Commute (word s hn p u) (word s hn q v) := by
  by_cases hus : u.length ≤ M
  · exact hc p q u v hus hv hpq hqp
  cases u with
  | nil => simp at hus
  | cons a u =>
    obtain ⟨c, hci, hcj, hck, hcl⟩ := exists_fresh hn p.row p.col q.row q.col
    have he := positive_next s hn hM hp hc p.row c p.col hci.symm hcj p.ne
      [a] u (by simp) (by simp only [List.length_cons] at hus; omega)
      (by simp only [List.length_cons, List.length_nil] at *; omega)
    rw [show word s hn p (a :: u) =
      bracket (word s hn ⟨p.row, c, hci.symm⟩ [a]) (word s hn ⟨c, p.col, hcj⟩ u) from he.symm]
    apply CommutatorCalculus.commute_bracket_left
    · exact hc _ _ _ _ (by simp; omega) hv hck hqp
    · exact hc _ _ _ _ (by simp only [List.length_cons] at hu; omega) hv hpq hcl

 theorem commute_next (s : Seed n α G) (hn : 5 ≤ n) {M : ℕ} (hM : 2 ≤ M)
    (hp : ProductUpTo (word s hn) M) (hc : CommuteUpTo (word s hn) M) :
    CommuteUpTo (word s hn) (M + 1) := by
  intro p q u v hu hv hpq hqp
  by_cases hus : u.length ≤ M
  · exact (commute_next_short s hn hM hp hc q p v u hv hus hqp.symm hpq.symm).symm
  cases u with
  | nil => simp at hus
  | cons a u =>
    obtain ⟨c, hci, hcj, hck, hcl⟩ := exists_fresh hn p.row p.col q.row q.col
    have he := positive_next s hn hM hp hc p.row c p.col hci.symm hcj p.ne
      [a] u (by simp) (by simp only [List.length_cons] at hus; omega)
      (by simp only [List.length_cons, List.length_nil] at *; omega)
    rw [show word s hn p (a :: u) =
      bracket (word s hn ⟨p.row, c, hci.symm⟩ [a]) (word s hn ⟨c, p.col, hcj⟩ u) from he.symm]
    apply CommutatorCalculus.commute_bracket_left
    · exact (commute_next_short s hn hM hp hc q ⟨p.row, c, hci.symm⟩ v [a] hv (by simp; omega)
        hqp.symm hck.symm).symm
    · exact (commute_next_short s hn hM hp hc q ⟨c, p.col, hcj⟩ v u hv
        (by simp only [List.length_cons] at hu; omega) hcl.symm hpq.symm).symm

 theorem bracket_square {a b : G} (ha : a ^ 2 = 1) (hc : Commute (bracket a b) a) :
    bracket a b ^ 2 = 1 := by
  have haa : a * a = 1 := by simpa only [pow_two] using ha
  have hai : a⁻¹ = a := (eq_inv_of_mul_eq_one_left haa).symm
  have hinv : bracket a b = (bracket a b)⁻¹ := by
    calc
      bracket a b = a * bracket a b * a⁻¹ := (CommutatorCalculus.conj_of_commute hc.symm).symm
      _ = (bracket a b)⁻¹ := by
        simp only [bracket, mul_inv_rev, inv_inv, hai]
        simp only [← mul_assoc, haa, one_mul]
  rw [pow_two]
  conv_lhs => lhs; rw [hinv]
  exact inv_mul_cancel _

 theorem squares_next (s : Seed n α G) (hn : 5 ≤ n) {M : ℕ} (hM : 2 ≤ M)
    (hp : ProductUpTo (word s hn) M) (hc : CommuteUpTo (word s hn) M)
    (hs : SquaresUpTo (word s hn) M) : SquaresUpTo (word s hn) (M + 1) := by
  intro p u hu
  by_cases hus : u.length ≤ M
  · exact hs p u hus
  cases u with
  | nil => simp at hus
  | cons a u =>
    let c := middle hn p
    have hci : c ≠ p.row := middle_ne_row hn p
    have hcj : c ≠ p.col := middle_ne_col hn p
    have he := positive_next s hn hM hp hc p.row c p.col hci.symm hcj p.ne
      [a] u (by simp) (by simp only [List.length_cons] at hus; omega)
      (by simp only [List.length_cons, List.length_nil] at *; omega)
    have he' : word s hn p (a :: u) =
      bracket (word s hn ⟨p.row, c, hci.symm⟩ [a]) (word s hn ⟨c, p.col, hcj⟩ u) := he.symm
    rw [he']
    apply bracket_square (hs _ _ (by simp; omega))
    rw [← he']
    exact commute_next s hn hM hp hc p ⟨p.row, c, hci.symm⟩ _ _ hu
      (by simp only [List.length_cons, List.length_nil]; omega) p.ne.symm hci.symm

 theorem product_next (s : Seed n α G) (hn : 5 ≤ n) {M : ℕ} (hM : 2 ≤ M)
    (hp : ProductUpTo (word s hn) M) (hc : CommuteUpTo (word s hn) M) :
    ProductUpTo (word s hn) (M + 1) := by
  intro i j k hij hjk hik u v huv
  by_cases hsmall : u.length + v.length ≤ M
  · exact hp i j k hij hjk hik u v hsmall
  have hc' := commute_next s hn hM hp hc
  cases u with
  | nil =>
    cases v with
    | nil => simp at hsmall
    | cons a v =>
      obtain ⟨c, hci, hcj, hck, _⟩ := exists_fresh hn i j k k
      have hv : 0 < v.length := by simp only [List.length_nil, List.length_cons] at hsmall; omega
      have hvl : v.length ≤ M := by simp only [List.length_nil, List.length_cons] at huv; omega
      have hpos := positive_next s hn hM hp hc j c k hcj.symm hck hjk [a] v
        (by simp) hv (by simp only [List.length_cons, List.length_nil] at *; omega)
      have hassoc := reassociate_of (word s hn) hc' i j c k hij hci.symm hik
        hcj.symm hjk hck [] [a] v
        (by simp only [List.length_nil, List.length_cons]; omega)
        (by simp only [List.length_nil, List.length_cons] at *; omega)
        (hp i j c hij hcj.symm hci.symm [] [a] (by simp; omega)) hpos
      calc
        bracket (word s hn ⟨i, j, hij⟩ []) (word s hn ⟨j, k, hjk⟩ (a :: v)) =
            bracket (word s hn ⟨i, c, hci.symm⟩ [a]) (word s hn ⟨c, k, hck⟩ v) := by
              simpa using hassoc.symm
        _ = word s hn ⟨i, k, hik⟩ ([] ++ a :: v) :=
          positive_next s hn hM hp hc i c k hci.symm hck hik [a] v (by simp) hv
            (by simp only [List.length_nil, List.length_cons] at *; omega)
  | cons a u =>
    cases v with
    | nil =>
      obtain ⟨c, hci, hcj, hck, _⟩ := exists_fresh hn i j k k
      have hu : 0 < u.length := by simp only [List.length_nil, List.length_cons] at hsmall; omega
      have hul : u.length ≤ M := by simp only [List.length_nil, List.length_cons] at huv; omega
      have hpos := positive_next s hn hM hp hc i c j hci.symm hcj hij [a] u
        (by simp) hu (by simp only [List.length_cons, List.length_nil] at *; omega)
      have hassoc := reassociate_of (word s hn) hc' i c j k hci.symm hij hik
        hcj hck hjk [a] u []
        (by simp only [List.length_nil, List.length_cons] at *; omega)
        (by simp only [List.length_nil]; omega)
        hpos (hp c j k hcj hjk hck u [] (by simpa using hul))
      calc
        bracket (word s hn ⟨i, j, hij⟩ (a :: u)) (word s hn ⟨j, k, hjk⟩ []) =
            bracket (word s hn ⟨i, c, hci.symm⟩ [a]) (word s hn ⟨c, k, hck⟩ u) := by
              simpa using hassoc
        _ = word s hn ⟨i, k, hik⟩ ((a :: u) ++ []) := by
          simpa using positive_next s hn hM hp hc i c k hci.symm hck hik [a] u
            (by simp) hu (by simp only [List.length_cons, List.length_nil] at *; omega)
    | cons b v =>
      exact positive_next s hn hM hp hc i j k hij hjk hik (a :: u) (b :: v)
        (by simp) (by simp) huv

 theorem good (s : Seed n α G) (hn : 5 ≤ n) (N : ℕ) : Good (word s hn) N := by
  induction N with
  | zero => exact base_good s hn 0 (by omega)
  | succ M ih =>
    by_cases hM : M < 2
    · exact base_good s hn (M + 1) (by omega)
    · exact ⟨product_next s hn (by omega) ih.1 ih.2.1,
        commute_next s hn (by omega) ih.1 ih.2.1,
        squares_next s hn (by omega) ih.1 ih.2.1 ih.2.2⟩

 theorem product (s : Seed n α G) (hn : 5 ≤ n)
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (u v : List α) :
    bracket (word s hn ⟨i, j, hij⟩ u) (word s hn ⟨j, k, hjk⟩ v) =
      word s hn ⟨i, k, hik⟩ (u ++ v) :=
  (good s hn (u.length + v.length)).1 i j k hij hjk hik u v le_rfl

 theorem commute (s : Seed n α G) (hn : 5 ≤ n)
    (p q : Root n) (u v : List α) (hpq : p.col ≠ q.row) (hqp : p.row ≠ q.col) :
    Commute (word s hn p u) (word s hn q v) :=
  (good s hn (max u.length v.length)).2.1 p q u v (le_max_left _ _) (le_max_right _ _) hpq hqp

 theorem square (s : Seed n α G) (hn : 5 ≤ n) (p : Root n) (u : List α) :
    word s hn p u ^ 2 = 1 := (good s hn u.length).2.2 p u le_rfl

abbrev Polynomial (α : Type u) := MonoidAlgebra (ZMod 2) (FreeMonoid α)

open scoped IsMulCommutative

noncomputable def rootSubgroup (s : Seed n α G) (hn : 5 ≤ n) (p : Root n) : Subgroup G :=
  Subgroup.closure (Set.range (word s hn p))

instance rootSubgroup_comm (s : Seed n α G) (hn : 5 ≤ n) (p : Root n) :
    IsMulCommutative (rootSubgroup s hn p) := by
  apply Subgroup.isMulCommutative_closure
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩ _
  exact commute s hn p p u v p.ne.symm p.ne

noncomputable def rootWord (s : Seed n α G) (hn : 5 ≤ n) (p : Root n) (w : List α) :
    rootSubgroup s hn p := ⟨word s hn p w, Subgroup.subset_closure ⟨w, rfl⟩⟩

noncomputable def coefficient (s : Seed n α G) (hn : 5 ≤ n) (p : Root n) (w : List α) :
    ZMod 2 →+ Additive (rootSubgroup s hn p) where
  toFun a := Additive.ofMul (if a = 0 then 1 else rootWord s hn p w)
  map_zero' := by simp
  map_add' := by
    intro a b
    have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases h01 a with rfl | rfl <;> rcases h01 b with rfl | rfl
    all_goals apply Additive.toMul.injective; apply Subtype.ext
    all_goals simp only [toMul_ofMul, toMul_add]
    all_goals try rw [show (1 : ZMod 2) + 1 = 0 by decide]
    all_goals simp [rootWord]
    simpa only [pow_two] using (square s hn p w).symm

noncomputable def poly (s : Seed n α G) (hn : 5 ≤ n) (p : Root n) (f : Polynomial α) : G :=
  ((Finsupp.liftAddHom (fun w : FreeMonoid α => coefficient s hn p w.toList) f.coeff).toMul : G)

@[simp] theorem poly_zero (s : Seed n α G) (hn : 5 ≤ n) (p : Root n) :
    poly s hn p 0 = 1 := by simp [poly]

 theorem poly_add (s : Seed n α G) (hn : 5 ≤ n) (p : Root n) (f g : Polynomial α) :
    poly s hn p (f + g) = poly s hn p f * poly s hn p g := by
  simp [poly]

@[simp] theorem poly_single (s : Seed n α G) (hn : 5 ≤ n) (p : Root n) (w : FreeMonoid α) :
    poly s hn p (MonoidAlgebra.single w 1) = word s hn p w.toList := by
  simp [poly, coefficient, rootWord]

 theorem closure_commute {S T : Set G}
    (h : ∀ x ∈ S, ∀ y ∈ T, Commute x y) {x y : G}
    (hx : x ∈ Subgroup.closure S) (hy : y ∈ Subgroup.closure T) : Commute x y := by
  have hle : Subgroup.closure S ≤ Subgroup.centralizer T :=
    (Subgroup.closure_le _).mpr (fun a ha =>
      Subgroup.mem_centralizer_iff.mpr (fun b hb => (h a ha b hb).eq.symm))
  have hxc : x ∈ Subgroup.centralizer (Subgroup.closure T : Set G) := by
    rw [Subgroup.centralizer_closure]
    exact hle hx
  exact (Subgroup.mem_centralizer_iff.mp hxc y hy).symm

 theorem poly_mem (s : Seed n α G) (hn : 5 ≤ n) (p : Root n) (f : Polynomial α) :
    poly s hn p f ∈ rootSubgroup s hn p :=
  (Finsupp.liftAddHom (fun w : FreeMonoid α => coefficient s hn p w.toList) f.coeff).toMul.property

 theorem poly_commute (s : Seed n α G) (hn : 5 ≤ n)
    (p q : Root n) (f g : Polynomial α) (hpq : p.col ≠ q.row) (hqp : p.row ≠ q.col) :
    Commute (poly s hn p f) (poly s hn q g) := by
  apply closure_commute (S := Set.range (word s hn p)) (T := Set.range (word s hn q))
    ?_ (poly_mem s hn p f) (poly_mem s hn q g)
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
  exact commute s hn p q u v hpq hqp

 theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 :=
  (of_decide_eq_true (by rfl) : ∀ a : ZMod 2, a = 0 ∨ a = 1) a

 theorem poly_product (s : Seed n α G) (hn : 5 ≤ n)
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (f g : Polynomial α) :
    bracket (poly s hn ⟨i, j, hij⟩ f) (poly s hn ⟨j, k, hjk⟩ g) =
      poly s hn ⟨i, k, hik⟩ (f * g) := by
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp [bracket]
  | add f₁ f₂ h₁ h₂ =>
    rw [poly_add, CommutatorCalculus.mul_left, h₂, h₁,
      CommutatorCalculus.conj_of_commute (poly_commute s hn _ _ f₁ (f₂ * g) hij.symm hik),
      add_mul, poly_add]
    exact (poly_commute s hn _ _ (f₂ * g) (f₁ * g) hik.symm hik).eq
  | single u a =>
    rcases zmod_two_cases a with rfl | rfl
    · simp [bracket]
    · induction g using MonoidAlgebra.induction_linear with
      | zero => simp [bracket]
      | add g₁ g₂ h₁ h₂ =>
        rw [poly_add, CommutatorCalculus.mul_right, h₁, h₂, mul_add, poly_add]
        have hconj := CommutatorCalculus.conj_of_commute
          (poly_commute s hn ⟨j, k, hjk⟩ ⟨i, k, hik⟩ g₁ (MonoidAlgebra.single u 1 * g₂)
            hik.symm hjk)
        simpa only [mul_assoc] using congrArg
          (fun x => poly s hn ⟨i, k, hik⟩ (MonoidAlgebra.single u 1 * g₁) * x) hconj
      | single v b =>
        rcases zmod_two_cases b with rfl | rfl
        · simp [bracket]
        · rw [MonoidAlgebra.single_mul_single, one_mul, poly_single, poly_single, poly_single]
          exact product s hn i j k hij hjk hik u.toList v.toList

noncomputable def lift (s : Seed n α G) (hn : 5 ≤ n) : Steinberg n (Polynomial α) →* G :=
  Steinberg.lift (poly s hn) (poly_add s hn)
    (fun p q h₁ h₂ f g => poly_commute s hn p q f g h₁ h₂) (poly_product s hn)

end MonomialCompletion

namespace FiniteSteinbergPresentation

open MonomialCompletion

variable {n : ℕ} {α : Type u}

abbrev ShortWord (α : Type u) := {w : List α // w.length ≤ 2}
abbrev Gen (n : ℕ) (α : Type u) := Root n × ShortWord α

instance root_finite (n : ℕ) : Finite (Root n) :=
  Finite.of_injective (fun p : Root n => (p.row, p.col)) (by
    rintro ⟨i, j, hij⟩ ⟨k, l, hkl⟩ he
    have hi : i = k := congrArg Prod.fst he
    have hj : j = l := congrArg Prod.snd he
    subst k; subst l
    rfl)

def shortWordMap : Unit ⊕ (α ⊕ α × α) → ShortWord α
  | .inl _ => ⟨[], by simp⟩
  | .inr (.inl a) => ⟨[a], by simp⟩
  | .inr (.inr (a, b)) => ⟨[a, b], by simp⟩

instance shortWord_finite [Finite α] : Finite (ShortWord α) :=
  Finite.of_surjective shortWordMap (by
    rintro ⟨w, hw⟩
    match w with
    | [] => exact ⟨.inl (), rfl⟩
    | [a] => exact ⟨.inr (.inl a), rfl⟩
    | [a, b] => exact ⟨.inr (.inr (a, b)), rfl⟩
    | _ :: _ :: _ :: _ => simp only [List.length_cons] at hw; omega)

def gen (p : Root n) (w : ShortWord α) : FreeGroup (Gen n α) := FreeGroup.of (p, w)

inductive Rel (n : ℕ) (α : Type u) : FreeGroup (Gen n α) → Prop
  | square (p : Root n) (w : ShortWord α) : Rel n α (gen p w ^ 2)
  | commute (p q : Root n) (h₁ : p.col ≠ q.row) (h₂ : p.row ≠ q.col)
      (u v : ShortWord α) : Rel n α (bracket (gen p u) (gen q v))
  | product (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
      (u v : ShortWord α) (h : u.val.length + v.val.length ≤ 2) :
      Rel n α (bracket (gen ⟨i, j, hij⟩ u) (gen ⟨j, k, hjk⟩ v) *
        (gen ⟨i, k, hik⟩ ⟨u.val ++ v.val, by simpa only [List.length_append] using h⟩)⁻¹)

 theorem rel_finite [Finite α] : {r | Rel n α r}.Finite := by
  let S₁ := Set.range (fun g : Gen n α => FreeGroup.of g ^ 2)
  let S₂ := Set.range (fun g : Gen n α × Gen n α => bracket (FreeGroup.of g.1) (FreeGroup.of g.2))
  let S₃ := Set.range (fun g : Gen n α × Gen n α × Gen n α =>
    bracket (FreeGroup.of g.1) (FreeGroup.of g.2.1) * (FreeGroup.of g.2.2)⁻¹)
  apply ((Set.finite_range _).union ((Set.finite_range _).union (Set.finite_range _)) :
    (S₁ ∪ (S₂ ∪ S₃)).Finite).subset
  intro r hr
  cases hr with
  | square p w => exact Or.inl ⟨(p, w), rfl⟩
  | commute p q h₁ h₂ u v => exact Or.inr (Or.inl ⟨((p, u), (q, v)), rfl⟩)
  | product i j k hij hjk hik u v h =>
    exact Or.inr (Or.inr ⟨((⟨i, j, hij⟩, u), (⟨j, k, hjk⟩, v),
      (⟨i, k, hik⟩, ⟨u.val ++ v.val, by simpa only [List.length_append] using h⟩)), rfl⟩)

end FiniteSteinbergPresentation
end SourceBurnside
end

end OAI
