import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.Total

namespace OAI

namespace LargeIndependentSets.ShortestPaths

structure Capped (B : ℕ) where
  val : ℕ
  bound : val ≤ B+1
  deriving DecidableEq

namespace Capped

@[ext] lemma ext {B : ℕ} {a b : Capped B} (h : a.val=b.val) : a=b := by
  cases a; cases b; simp_all

def finEquiv (B : ℕ) : Fin (B+2) ≃ Capped B where
  toFun a := ⟨a.val,by omega⟩
  invFun a := ⟨a.val,by have := a.bound; omega⟩
  left_inv a := by rfl
  right_inv a := by rfl

instance (B : ℕ) : Fintype (Capped B) := Fintype.ofEquiv _ (finEquiv B)

instance (B : ℕ) : Min (Capped B) := ⟨fun a b => if a.val ≤ b.val then a else b⟩
instance (B : ℕ) : Add (Capped B) := ⟨fun a b => ⟨min (a.val+b.val) (B+1),min_le_right _ _⟩⟩

lemma min_val {B : ℕ} (a b : Capped B) : (min a b).val = min a.val b.val := by
  change (if a.val ≤ b.val then a else b).val = _
  split <;> simp_all [le_of_not_ge]

lemma add_val {B : ℕ} (a b : Capped B) : (a+b).val = min (a.val+b.val) (B+1) := rfl

def clip (B : ℕ) (c : ℕ∞) : Capped B :=
  ⟨if c=⊤ then B+1 else min c.toNat (B+1),by split <;> simp⟩

@[simp] lemma clip_top (B : ℕ) : (clip B ⊤).val = B+1 := by simp [clip]
@[simp] lemma clip_nat (B n : ℕ) : (clip B (n:ℕ∞)).val = min n (B+1) := by simp [clip]

lemma clip_min (B : ℕ) (a b : ℕ∞) : clip B (min a b) = min (clip B a) (clip B b) := by
  apply ext
  rw [min_val]
  induction a using ENat.recTopCoe with
  | top => simp [min_eq_right (clip B b).bound]
  | coe a =>
    induction b using ENat.recTopCoe with
    | top => simp
    | coe b =>
      have he : min (a:ℕ∞) (b:ℕ∞) = ((min a b : ℕ):ℕ∞) := by exact_mod_cast rfl
      rw [he]
      simp only [clip_nat]
      omega

lemma clip_add (B : ℕ) (a b : ℕ∞) : clip B (a+b) = clip B a + clip B b := by
  apply ext
  rw [add_val]
  induction a using ENat.recTopCoe with
  | top => simp [clip_top]
  | coe a =>
    induction b using ENat.recTopCoe with
    | top => simp [clip_top]
    | coe b =>
      rw [← ENat.natCast_add]
      simp only [clip_nat]
      omega

lemma clip_le_iff (B : ℕ) (c : ℕ∞) {t : ℕ} (ht : t≤B) :
    (clip B c).val ≤ t ↔ c ≤ (t:ℕ∞) := by
  induction c using ENat.recTopCoe with
  | top => simp; omega
  | coe c => simp only [clip_nat,ENat.natCast_le_natCast]; omega

lemma closure_exact {X : Type*} (B : ℕ) (a : X→X→ℕ∞) (ks : List X) (i j : X) :
    closure (fun x y => clip B (a x y)) ks i j = clip B (closure a ks i j) := by
  exact (congrFun (congrFun (closure_map (clip B) (clip_min B) (clip_add B) a ks) i) j).symm

end Capped
end LargeIndependentSets.ShortestPaths

namespace LargeIndependentSets.ShortestPaths.Capped

abbrev Matrix (B n : ℕ) := Vector (Vector (Capped B) n) n

def Matrix.get {B n : ℕ} (a : Matrix B n) (i j : Fin n) : Capped B := a[i.val][j.val]

def Matrix.pivot {B n : ℕ} (a : Matrix B n) (k : Fin n) : Matrix B n :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => ShortestPaths.pivot a.get k i j))

def Matrix.run {B n : ℕ} (a : Matrix B n) : List (Fin n) → Matrix B n
  | [] => a
  | k::ks => (a.pivot k).run ks

lemma Matrix.run_get {B n : ℕ} (a : Matrix B n) (ks : List (Fin n)) :
    (a.run ks).get = closure a.get ks := by
  induction ks generalizing a with
  | nil => rfl
  | cons k ks ih =>
    rw [Matrix.run,ih]
    simp only [closure]
    congr 1
    funext i j
    simp [Matrix.pivot,Matrix.get]

def Matrix.allPairs {B n : ℕ} (a : Matrix B n) : Matrix B n := a.run (List.finRange n)

def Matrix.ofInteger (B : ℕ) {n : ℕ} (a : ShortestPaths.Matrix n) : Matrix B n :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => clip B (a.get i j)))

theorem Matrix.allPairs_exact (B : ℕ) {n : ℕ} (a : ShortestPaths.Matrix n) (i j : Fin n) :
    ((Matrix.ofInteger B a).allPairs).get i j = clip B (a.allPairs.get i j) := by
  rw [Matrix.allPairs,Matrix.run_get,ShortestPaths.Matrix.allPairs,ShortestPaths.Matrix.run_get]
  have he : (Matrix.ofInteger B a).get = fun x y => clip B (a.get x y) := by
    funext x y
    simp [Matrix.ofInteger,Matrix.get]
  rw [he,closure_exact]

theorem Matrix.threshold_exact (B : ℕ) {n : ℕ} (a : ShortestPaths.Matrix n) (i j : Fin n)
    {t : ℕ} (ht : t≤B) :
    (((Matrix.ofInteger B a).allPairs).get i j).val ≤ t ↔ a.allPairs.get i j ≤ (t:ℕ∞) := by
  rw [Matrix.allPairs_exact,clip_le_iff B _ ht]

end LargeIndependentSets.ShortestPaths.Capped

end OAI
