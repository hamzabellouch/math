import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.List.Induction
import Mathlib.Data.Set.Image
import Mathlib.GroupTheory.FreeGroup.Reduce

namespace OAI

namespace Generator

/-! All alternating word shapes, allowing either algebra at either endpoint. -/
section
variable {A : Type*}

def alternatingFrom (S T : Set A) : Bool → List A → Prop
  | _,[] => True
  | b,x::xs => x ∈ (if b then S else T) ∧ alternatingFrom S T (!b) xs

def alternatingSlotSets (S T : Set A) : Bool → ℕ → List (Set A)
  | _,0 => []
  | b,n+1 => (if b then S else T)::alternatingSlotSets S T (!b) n

theorem alternatingFrom_slots (S T : Set A) (b : Bool) (xs : List A) :
    alternatingFrom S T b xs ↔
      List.Forall₂ (fun s x => x ∈ s) (alternatingSlotSets S T b xs.length) xs := by
  induction xs generalizing b with
  | nil => simp [alternatingFrom,alternatingSlotSets]
  | cons x xs ih => simp [alternatingFrom,alternatingSlotSets,ih]

theorem alternatingSlotSets_length (S T : Set A) (b : Bool) (n : ℕ) :
    (alternatingSlotSets S T b n).length=n := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => simp [alternatingSlotSets,ih]

/-- Vanishing of every nonempty alternating word from two specified sets. -/
def alternatingMomentsZero {K : Type*} [Zero K] [Monoid A]
    (φ : A → K) (S T : Set A) : Prop :=
  ∀ b xs,xs ≠ [] → alternatingFrom S T b xs → φ xs.prod=0

end

section
variable {A B K : Type*}

theorem alternatingFrom_image (f : A → B) (S T : Set A) (b : Bool) (xs : List B)
    (hx : alternatingFrom (f '' S) (f '' T) b xs) :
    ∃ ys : List A,ys.map f=xs ∧ alternatingFrom S T b ys := by
  induction xs generalizing b with
  | nil => exact ⟨[],rfl,True.intro⟩
  | cons x xs ih =>
    have hx' : x ∈ f '' (if b then S else T) := by cases b <;> exact hx.1
    obtain ⟨y,hy,rfl⟩ := hx'
    obtain ⟨ys,rfl,hys⟩ := ih (!b) hx.2
    exact ⟨y::ys,rfl,hy,hys⟩

theorem alternatingMomentsZero_map [Monoid A] [Monoid B] [Zero K]
    (f : A →* B) (φ : A → K) (ψ : B → K) (hφ : ∀ a,ψ (f a)=φ a)
    (S T : Set A) (hm : alternatingMomentsZero φ S T) :
    alternatingMomentsZero ψ (f '' S) (f '' T) := by
  intro b xs hn hx
  obtain ⟨ys,rfl,hy⟩ := alternatingFrom_image f S T b xs hx
  have hne : ys ≠ [] := by intro he; exact hn (by simp [he])
  rw [← map_list_prod,hφ]
  exact hm b ys hne hy

end

/-! Splitting a reduced word at its first occurrence of a specified generator. -/

theorem word_split_first {A : Type*} [DecidableEq A] (n : A)
    (w : List (A × Bool)) (h : ∃ x ∈ w,x.1=n) :
    ∃ a s b,w=a++(n,s)::b ∧ ∀ x ∈ a,x.1 ≠ n := by
  induction w with
  | nil => simp at h
  | cons x w ih =>
    by_cases hx : x.1=n
    · exact ⟨[],x.2,w,by cases x; simp_all,by simp⟩
    · obtain ⟨a,s,b,he,ha⟩ := ih (by
        obtain ⟨y,hy,hn⟩ := h
        rcases List.mem_cons.mp hy with rfl | hy
        · exact (hx hn).elim
        · exact ⟨y,hy,hn⟩)
      refine ⟨x::a,s,b,by simp [he],?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact ha y hy

theorem reduced_append_left {A : Type*} {a b : List (A × Bool)}
    (h : FreeGroup.IsReduced (a++b)) : FreeGroup.IsReduced a :=
  List.IsChain.left_of_append h

theorem reduced_append_right {A : Type*} {a b : List (A × Bool)}
    (h : FreeGroup.IsReduced (a++b)) : FreeGroup.IsReduced b :=
  List.IsChain.right_of_append h

theorem reduced_tail {A : Type*} {a : A × Bool} {w : List (A × Bool)}
    (h : FreeGroup.IsReduced (a::w)) : FreeGroup.IsReduced w :=
  List.IsChain.tail h

/-! Noncommutative ordered row words and coefficient majorization, without commuting-row assumptions. -/
variable {R : Type*} [Semiring R]

def orderedWords : List R → ℕ → R
  | [], 0 => 1
  | [], _ + 1 => 0
  | _ :: _, 0 => 1
  | a :: as, d + 1 => a * orderedWords (a :: as) d + orderedWords as (d + 1)
termination_by xs d => (d, xs.length)

@[simp] theorem orderedWords_zero (xs : List R) : orderedWords xs 0 = 1 := by
  cases xs <;> simp [orderedWords]

@[simp] theorem orderedWords_nil (d : ℕ) : orderedWords ([] : List R) d = if d = 0 then 1 else 0 := by
  cases d <;> simp [orderedWords]

/-- Grouping nondecreasing row words by the number of initial first-row letters. -/
theorem orderedWords_cons (a : R) (as : List R) (d : ℕ) :
    orderedWords (a :: as) d =
      ∑ k ∈ Finset.range (d + 1), a ^ k * orderedWords as (d - k) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [orderedWords, ih]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [pow_zero, one_mul, Nat.sub_zero, Nat.add_sub_add_right]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_succ', mul_assoc]

variable [PartialOrder R] [IsOrderedRing R]

theorem orderedWords_nonneg (xs : List R) (hx : ∀ a ∈ xs, 0 ≤ a) (d : ℕ) :
    0 ≤ orderedWords xs d := by
  induction d generalizing xs with
  | zero => simp
  | succ d ih =>
    induction xs with
    | nil => simp
    | cons a as iht =>
      rw [orderedWords]
      exact add_nonneg (mul_nonneg (hx a (by simp)) (ih _ hx))
        (iht (fun b hb => hx b (by simp [hb])))

theorem orderedWords_tail_le (a : R) (as : List R)
    (ha : 0 ≤ a) (has : ∀ b ∈ as, 0 ≤ b) (d : ℕ) :
    orderedWords as d ≤ orderedWords (a :: as) d := by
  cases d with
  | zero => simp
  | succ d =>
    rw [orderedWords]
    exact le_add_of_nonneg_left (mul_nonneg ha
      (orderedWords_nonneg _ (by simpa using And.intro ha has) d))

/-- Choosing the first row of a nondecreasing word gives a subset of all choices. -/
theorem orderedWords_step_le (xs : List R) (hx : ∀ a ∈ xs, 0 ≤ a) (d : ℕ) :
    orderedWords xs (d + 1) ≤ xs.sum * orderedWords xs d := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    have ha := hx a (by simp)
    have has : ∀ b ∈ as, 0 ≤ b := fun b hb => hx b (by simp [hb])
    calc
      orderedWords (a :: as) (d + 1) =
          a * orderedWords (a :: as) d + orderedWords as (d + 1) := by rw [orderedWords]
      _ ≤ a * orderedWords (a :: as) d + as.sum * orderedWords as d :=
        add_le_add le_rfl (ih has)
      _ ≤ a * orderedWords (a :: as) d + as.sum * orderedWords (a :: as) d :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (orderedWords_tail_le a as ha has d)
          (List.sum_nonneg has))
      _ = _ := by rw [List.sum_cons, add_mul]

/-- All-degree bound by the full distributive power, without commuting factors. -/
theorem orderedWords_le_sum_pow (xs : List R) (hx : ∀ a ∈ xs, 0 ≤ a) (d : ℕ) :
    orderedWords xs d ≤ xs.sum ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    calc
      _ ≤ xs.sum * orderedWords xs d := orderedWords_step_le xs hx d
      _ ≤ xs.sum * xs.sum ^ d := mul_le_mul_of_nonneg_left ih (List.sum_nonneg hx)
      _ = _ := (pow_succ' _ _).symm

end Generator

end OAI
