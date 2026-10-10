import OAI.Analysis.FourierLLogL.Dyadic.Discrete
/-! # Grid distance and elementary counting -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic
open Law Period Real

variable {M : ℕ}

def rad (x : Grid M) : ℝ := ↑(min x.val (-x).val)
def diam (x : Grid M) : ℝ := side M * rad x

def liftInt (x : Grid M) : ℤ := if x.val ≤ (-x).val then x.val else -↑(-x).val

lemma rad_abs (x : Grid M) : rad x = |(liftInt x:ℝ)| := by
  unfold liftInt rad
  split_ifs with h
  · rw [min_eq_left h, Int.cast_natCast,abs_of_nonneg (by positivity)]
  · rw [min_eq_right (by omega),Int.cast_neg, abs_neg,Int.cast_natCast,abs_of_nonneg (by positivity)]

lemma liftInt_cast (x : Grid M) : (liftInt x:Grid M) = x := by unfold liftInt; split_ifs <;> simp
lemma rad_even (x : Grid M) : rad (-x) = rad x := by simp [rad,min_comm]
lemma diam_even (x : Grid M) : diam (-x) = diam x := by rw [diam,diam,rad_even]

lemma rad_nonneg (x : Grid M) : 0 ≤ rad x := by rw [rad_abs]; positivity
lemma diam_nonneg (x : Grid M) : 0 ≤ diam x := mul_nonneg (side_pos _).le (rad_nonneg _)

lemma pos_nonneg (x : Grid M) : 0 ≤ pos x := mul_nonneg (by positivity) (side_pos _).le
lemma pos_lt (x : Grid M) : pos x < 1 := (atom_sub x (pos_mem x)).2
lemma pos_neg {x : Grid M} (hx : x≠0) : pos (-x) = 1-pos x := by
  have : NeZero x := ⟨hx⟩
  simp_rw [pos, ZMod.val_neg_of_ne_zero, Nat.cast_sub (ZMod.val_lt _).le, sub_mul,side_pow_two]
  push_cast
  rw [mul_inv_cancel₀ (by positivity)]

lemma diam_min (x : Grid M) : diam x = min (pos x) (pos (-x)) := by
  unfold diam rad pos
  rw [Nat.cast_min, mul_comm, min_mul_of_nonneg _ _ (side_pos _).le]

lemma diam_le_half (x : Grid M) : diam x ≤ 1/2 := by
  rw [diam_min]
  by_cases hx : x=0
  · subst x; simp [pos]
  · rw [pos_neg hx, min_le_iff]
    by_cases H : pos x ≤ 1/2
    · exact Or.inl H
    · exact Or.inr (by linarith)

lemma rad_le_val (x : Grid M) : rad x ≤ ↑x.val := by simp [rad]
lemma rad_le_nat (k : ℕ) : rad (k:Grid M) ≤ ↑k := by
  refine (rad_le_val _).trans ?_
  rw [ZMod.val_natCast]; exact_mod_cast (Nat.mod_le k (2^M))

lemma rad_le_int (k : ℤ) : rad (k:Grid M) ≤ |(k:ℝ)| := by
  cases k with
  | ofNat k => simpa using rad_le_nat (M:=M) k
  | negSucc k =>
    rw [show ((Int.negSucc k:ℤ):Grid M) = -((k+1:ℕ):Grid M) by simp, rad_even]
    convert rad_le_nat (M:=M) (k+1) using 1
    push_cast
    rw [abs_of_nonpos (by have H := Nat.cast_nonneg (α:=ℝ) k; linarith)]; ring

lemma rad_add (x y : Grid M) : rad (x+y) ≤ rad x+rad y := by
  have H := rad_le_int (M:=M) (liftInt x + liftInt y)
  rw [Int.cast_add,liftInt_cast,liftInt_cast,Int.cast_add] at H
  rw [rad_abs x,rad_abs y]
  exact H.trans (abs_add_le _ _)
lemma diam_add (x y : Grid M) : diam (x+y) ≤ diam x+diam y := by
  simp_rw [diam]; rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (rad_add _ _) (side_pos _).le

lemma pos_sub_val {x y : Grid M} (h : y.val ≤ x.val) : pos (x-y) = pos x-pos y := by
  simp [pos,ZMod.val_sub h,Nat.cast_sub h,sub_mul]

lemma diam_le_diff (x y : Grid M) : diam (x-y) ≤ |pos x-pos y| := by
  rcases le_total y.val x.val with h|h
  · exact le_trans (show diam (x-y) ≤ pos (x-y) by rw [diam_min]; exact min_le_left _ _)
      (by rw [pos_sub_val h]; exact le_abs_self _)
  rw [diam_min,neg_sub]
  exact (min_le_right _ _).trans (by rw [pos_sub_val h,abs_sub_comm]; exact le_abs_self _)

lemma phase_distance (s x y : Grid M) :
    ‖chi s x-chi s y‖ ≤ rad s * (8 * |pos x-pos y|) := by
  calc
    _ = ‖phase (liftInt s :ℝ) (pos x) - phase (liftInt s:ℝ) (pos y)‖ := by
      rw [← chi_cast,← chi_cast,liftInt_cast]
    _ ≤ _ := (norm_phase_sub _ _ _).trans (by rw [rad_abs s]; gcongr; linarith [pi_le_four])


def first (M m : ℕ) : Finset (Grid M) :=
  Finset.univ.filter fun x => x.val < m
lemma mem_first (m : ℕ) (x : Grid M) : x ∈ first M m ↔ x.val < m := by simp [first]

lemma first_eq_range (m : ℕ) (h : m ≤ 2^M) :
    first M m = (Finset.range m).image (fun k : ℕ => (k:Grid M)) := by
  ext x
  rw [mem_first,Finset.mem_image]
  constructor
  · intro hi; exact ⟨x.val,Finset.mem_range.mpr hi, ZMod.natCast_zmod_val _⟩
  · rintro ⟨k,hk,rfl⟩; rw [ZMod.val_natCast_of_lt ((Finset.mem_range.mp hk).trans_le h)]
    exact Finset.mem_range.mp hk

lemma range_inj {m : ℕ} (h : m ≤ 2^M) :
    Set.InjOn (fun k : ℕ => (k:Grid M)) (Finset.range m) := by
  intro i hi j hj HH
  have he := congrArg ZMod.val HH
  rwa [ZMod.val_natCast_of_lt ((Finset.mem_range.mp hi).trans_le h),
    ZMod.val_natCast_of_lt ((Finset.mem_range.mp hj).trans_le h)] at he

lemma first_card (m : ℕ) (h : m ≤ 2^M) : (first M m).card = m := by
  rw [first_eq_range m h,Finset.card_image_of_injOn (range_inj h), Finset.card_range]

lemma first_card_le (m : ℕ) : (first M m).card ≤ m := by
  rcases le_total m (2^M) with h | h
  · exact (first_card _ h).le
  · refine le_trans (Finset.card_le_univ _) ?_
    simpa [Grid] using h

lemma sum_first {E : Type*} [AddCommMonoid E] (m : ℕ) (h : m ≤ 2^M) (f : ℕ → E) :
    ∑ x ∈ first M m, f x.val = ∑ k ∈ Finset.range m, f k := by
  rw [first_eq_range _ h, Finset.sum_image]
  · exact Finset.sum_congr rfl fun i hi => by
      rw [ZMod.val_natCast_of_lt ((Finset.mem_range.mp hi).trans_le h)]
  intro i hi j hj h'
  exact range_inj h hi hj h'

lemma first_max : first M (2^M) = Finset.univ := by
  ext x; simp [first,ZMod.val_lt]

lemma sum_grid {E : Type*} [AddCommMonoid E] (f : ℕ → E) :
    ∑ x : Grid M, f x.val = ∑ k ∈ Finset.range (2^M), f k := by
  rw [← sum_first _ le_rfl, first_max]

def arc (M : ℕ) (r : ℝ) : Finset (Grid M) := Finset.univ.filter fun x => rad x ≤ r
lemma mem_arc (r : ℝ) (x : Grid M) : x ∈ arc M r ↔ rad x ≤ r := by simp [arc]

lemma arc_card_hi (M : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    ((arc M r).card :ℝ) ≤ 2*(r+1) := by
  let m := Nat.floor r +1
  have hin :
      arc M r ⊆ first M m ∪ (first M m).image Neg.neg := by
    intro x hx
    rw [mem_arc, rad, Nat.cast_min,min_le_iff] at hx
    rw [Finset.mem_union,Finset.mem_image,mem_first]
    rcases hx with H | H
    · exact Or.inl (Nat.lt_succ_of_le ((Nat.le_floor_iff hr).mpr H))
    exact Or.inr ⟨-x, (mem_first _ _).mpr (Nat.lt_succ_of_le ((Nat.le_floor_iff hr).mpr H)),neg_neg _⟩
  have h1 := (Finset.card_le_card hin).trans (Finset.card_union_le _ _)
  have h2 := Finset.card_image_le (s:=first M m) (f:=Neg.neg)
  have he : (arc M r).card ≤ 2*m := by have := first_card_le (M:=M) m; omega
  calc
    _ ≤ ((2*m:ℕ):ℝ) := Nat.cast_le.mpr he
    _ ≤ _ := by unfold m; push_cast; have H := Nat.floor_le hr; linarith

lemma arc_card_lo (M : ℕ) (r : ℝ) (_hr : 0 ≤ r) (h : r ≤ 2^M) :
    r ≤ ((arc M r).card:ℝ) := by
  let m := Nat.ceil r
  have hm : m ≤ 2^M := Nat.ceil_le.mpr (by exact_mod_cast h)
  have hh : first M m ⊆ arc M r := by
    intro x hx
    rw [mem_first] at hx; rw [mem_arc]
    exact (rad_le_val x).trans ((Nat.lt_ceil.mp hx).le)
  calc
    _ ≤ (m:ℝ) := Nat.le_ceil _
    _ ≤ _ := Nat.cast_le.mpr (by rw [← first_card m hm]; exact Finset.card_le_card hh)

lemma side_card (M : ℕ) : side M * (2:ℝ)^M = 1 := by rw [side_pow_two]; field_simp

lemma arc_length (M : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (uniform (Grid M)).prob (fun x => diam x ≤ r) ≤ 2*(r+side M) := by
  rw [prob_eq]
  have Heq :
      (∑ x : Grid M, if diam x ≤ r then uniform (Grid M) x else 0) =
        (arc M (r / side M)).card* side M := by
    have he : arc M (r / side M) = Finset.univ.filter fun x : Grid M => diam x ≤ r := by
      ext x
      simp [diam,arc,le_div_iff₀ (side_pos M),mul_comm]
    rw [← Finset.sum_filter,← he]
    simp [uniform_side]
  rw [Heq]
  calc
    _ ≤ (2*(r / side M +1))*side M := by
      apply mul_le_mul_of_nonneg_right (arc_card_hi M _ (div_nonneg hr (side_pos _).le)) (side_pos _).le
    _ = _ := by field_simp [(side_pos _).ne']

end FourierLLogL.Dyadic

end OAI
