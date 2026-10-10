import OAI.Combinatorics.FiniteCircle.Lower

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem segment_segment {α : Type*} (x : List α) (start size r len : ℕ)
    (h : r + len ≤ size) : segment (segment x start size) r len = segment x (start + r) len := by
  unfold segment
  rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]

theorem segment_append_left {α : Type*} (u v : List α) {start size : ℕ}
    (h : start + size ≤ u.length) : segment (u ++ v) start size = segment u start size := by
  unfold segment
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

theorem segment_append_right {α : Type*} (u v : List α) {start size : ℕ}
    (h : u.length ≤ start) : segment (u ++ v) start size = segment v (start - u.length) size := by
  unfold segment
  rw [List.drop_append, List.drop_eq_nil_of_le h, List.nil_append]

theorem slide_segment_before {α : Type*} (u v t : List α) (a b : α) {start size : ℕ}
    (h : start + size ≤ u.length) :
    segment (u ++ a :: (v ++ t)) start size = segment (u ++ v ++ b :: t) start size := by
  rw [segment_append_left _ _ h, List.append_assoc, segment_append_left _ _ h]

theorem slide_segment_after {α : Type*} (u v t : List α) (a b : α) {start size : ℕ}
    (h : u.length + v.length + 1 ≤ start) :
    segment (u ++ a :: (v ++ t)) start size = segment (u ++ v ++ b :: t) start size := by
  have h₁ : (u ++ a :: v).length ≤ start := by simp; omega
  have h₂ : (u ++ v ++ [b]).length ≤ start := by simp; omega
  rw [show u ++ a :: (v ++ t) = (u ++ a :: v) ++ t by simp,
    show u ++ v ++ b :: t = (u ++ v ++ [b]) ++ t by simp,
    segment_append_right _ _ h₁, segment_append_right _ _ h₂]
  congr 2
  simp

theorem slide_segment_shift {α : Type*} (u v t : List α) (a b : α) {start size : ℕ}
    (h₁ : u.length + 1 ≤ start) (h₂ : start + size ≤ u.length + v.length + 1) :
    segment (u ++ a :: (v ++ t)) start size =
      segment (u ++ v ++ b :: t) (start - 1) size := by
  rw [show u ++ a :: (v ++ t) = (u ++ [a]) ++ (v ++ t) by simp,
    segment_append_right (u ++ [a]) _ (by simp; omega),
    show u ++ v ++ b :: t = u ++ (v ++ b :: t) by simp,
    segment_append_right u _ (by omega),
    segment_append_left v t (by simp; omega),
    segment_append_left v (b :: t) (by omega)]
  congr 1
  simp only [List.length_append, List.length_singleton]
  omega

def windows {α : Type*} (x : List α) (start m s : ℕ) : List (List α) :=
  List.ofFn (fun r : Fin s => segment x (start + r) (m - s + 1))

@[simp] theorem length_windows {α : Type*} (x : List α) (start m s : ℕ) :
    (windows x start m s).length = s := List.length_ofFn

theorem windows_before {α : Type*} (u v t : List α) (a b : α)
    {start m s : ℕ} (_hs : 1 ≤ s) (hsm : s ≤ m) (hbef : start + m ≤ u.length) :
    windows (u ++ a :: (v ++ t)) start m s = windows (u ++ v ++ b :: t) start m s := by
  unfold windows
  congr 1
  funext r
  exact slide_segment_before _ _ _ _ _ (by have := r.isLt; omega)

theorem windows_after {α : Type*} (u v t : List α) (a b : α)
    {start m s : ℕ} (haft : u.length + v.length + 1 ≤ start) :
    windows (u ++ a :: (v ++ t)) start m s = windows (u ++ v ++ b :: t) start m s := by
  unfold windows
  congr 1
  funext r
  exact slide_segment_after _ _ _ _ _ (by omega)

theorem windows_shift {α : Type*} (u v t : List α) (a b : α)
    {start m s : ℕ} (hs : 1 ≤ s) (hsm : s ≤ m)
    (h₁ : u.length + 1 ≤ start) (h₂ : start + m ≤ u.length + v.length) :
    ∃ zs : List (List α), zs.length = s - 1 ∧
      zs <+ windows (u ++ a :: (v ++ t)) start m s ∧
      zs <+ windows (u ++ v ++ b :: t) start m s := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  let zs := List.ofFn (fun i : Fin r => segment (u ++ a :: (v ++ t)) (start + i.val + 1) (m - (r+1) + 1))
  refine ⟨zs, by simp [zs], ?_, ?_⟩
  · unfold windows
    rw [List.ofFn_succ]
    have he : zs = List.ofFn (fun i : Fin r => segment (u ++ a :: (v ++ t))
        (start + (i.succ : Fin (r+1))) (m - (r+1) + 1)) := by simp [zs, Nat.add_assoc]
    rw [he]
    exact List.Sublist.cons _ (List.Sublist.refl _)
  · unfold windows
    rw [List.ofFn_succ']
    have he : zs = List.ofFn (fun i : Fin r => segment (u ++ v ++ b :: t)
        (start + (i.castSucc : Fin (r+1))) (m - (r+1) + 1)) := by
      unfold zs
      congr 1
      funext i
      have hh := slide_segment_shift u v t a b (start := start + i.val + 1)
        (size := m - (r+1) + 1) (by omega) (by have := i.isLt; omega)
      simpa using hh
    rw [he]
    rw [List.concat_eq_append]
    exact List.sublist_append_left _ _

theorem block_location (p q m j : ℕ) (hm : 0 < m) (_hpq : p ≤ q)
    (hp : j ≠ p / m) (hq : j ≠ q / m) :
    (j * m + m ≤ p) ∨ (p + 1 ≤ j * m ∧ j * m + m ≤ q) ∨ (q + 1 ≤ j * m) := by
  by_cases hjp : j < p / m
  · left
    have h := (Nat.le_div_iff_mul_le hm).mp (by omega : j+1 ≤ p/m)
    nlinarith
  · have hstart : p + 1 ≤ j*m := by
      have h := (Nat.div_lt_iff_lt_mul hm).mp (by omega : p/m < j)
      omega
    by_cases hjq : j < q / m
    · right; left
      refine ⟨hstart, ?_⟩
      have h := (Nat.le_div_iff_mul_le hm).mp (by omega : j+1 ≤ q/m)
      nlinarith
    · right; right
      have h := (Nat.div_lt_iff_lt_mul hm).mp (by omega : q/m < j)
      omega

theorem windows_nonexceptional {α : Type*} (u v t : List α) (a b : α)
    {m s j : ℕ} (hs : 1 ≤ s) (hsm : s ≤ m)
    (hp : j ≠ u.length / m) (hq : j ≠ (u.length + v.length) / m) :
    ∃ zs : List (List α), s - 1 ≤ zs.length ∧
      zs <+ windows (u ++ a :: (v ++ t)) (j*m) m s ∧
      zs <+ windows (u ++ v ++ b :: t) (j*m) m s := by
  rcases block_location u.length (u.length+v.length) m j (by omega) (by omega) hp hq with h | h | h
  · have he := windows_before u v t a b hs hsm h
    exact ⟨_, by simp, .refl _, he ▸ List.Sublist.refl _⟩
  · obtain ⟨zs, hz, hx, hy⟩ := windows_shift u v t a b hs hsm h.1 h.2
    exact ⟨zs, hz.ge, hx, hy⟩
  · have he := windows_after u v t a b (m := m) (s := s) h
    exact ⟨_, by simp, .refl _, he ▸ List.Sublist.refl _⟩

theorem lcs_append_ge {α : Type*} (x y u v : List α) :
    lcs x y + lcs u v ≤ lcs (x ++ u) (y ++ v) := by
  obtain ⟨z, hzx, hzy, hz⟩ := lcs_exists x y
  obtain ⟨t, htu, htv, ht⟩ := lcs_exists u v
  simpa [List.length_append, hz, ht] using le_lcs (hzx.append htu) (hzy.append htv)

theorem deficit_append_le {α : Type*} (x y u v : List α) :
    deficit (x ++ u) (y ++ v) ≤ deficit x y + deficit u v := by
  have h := lcs_append_ge x y u v
  have hx := lcs_le_length_left x y
  have hu := lcs_le_length_left u v
  simp only [deficit, List.length_append]
  omega

theorem deficit_le_sum_blocks {α : Type*} {x y : List α} {b m : ℕ}
    (hx : x.length = b*m) (hy : y.length = b*m) :
    deficit x y ≤ ∑ j : Fin b, deficit (segment x (j*m) m) (segment y (j*m) m) := by
  induction b generalizing x y with
  | zero =>
    have hx0 : x = [] := List.length_eq_zero_iff.mp (by simpa using hx)
    have hy0 : y = [] := List.length_eq_zero_iff.mp (by simpa using hy)
    simp [hx0, hy0, deficit]
  | succ b ih =>
    have hxt : (x.drop m).length = b*m := by simp only [List.length_drop]; rw [hx, Nat.succ_mul]; omega
    have hyt : (y.drop m).length = b*m := by simp only [List.length_drop]; rw [hy, Nat.succ_mul]; omega
    have hd := deficit_append_le (x.take m) (y.take m) (x.drop m) (y.drop m)
    simp only [List.take_append_drop] at hd
    refine hd.trans ?_
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.zero_mul, segment, List.drop_zero]
    apply Nat.add_le_add_left
    convert ih hxt hyt using 1
    apply Finset.sum_congr rfl
    intro j _
    simp [segment, List.drop_drop, Fin.val_succ, Nat.add_mul, Nat.add_comm]

open scoped BigOperators List

open scoped BigOperators

end FiniteCircle

end OAI
