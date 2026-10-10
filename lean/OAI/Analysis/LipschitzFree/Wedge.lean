import Mathlib

namespace OAI

/-!
# Metric wedges and their contractive component retractions
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.MetricWedge
open scoped Classical
universe u
variable (M : ℕ → Type u) [∀ n, MetricSpace (M n)] (o : ∀ n, M n)

def Point := Option (Σ n, {x : M n // x ≠ o n})

instance [∀ n, Countable (M n)] : Countable (Point M o) :=
  inferInstanceAs (Countable (Option (Σ n, {x : M n // x ≠ o n})))

def base : Point M o := none

def distance : Point M o → Point M o → ℝ
  | none, none => 0
  | none, some ⟨n,x⟩ => dist x.val (o n)
  | some ⟨n,x⟩, none => dist x.val (o n)
  | some ⟨n,x⟩, some ⟨m,y⟩ =>
      if h : n = m then dist (h ▸ x.val) y.val else dist x.val (o n) + dist y.val (o m)

theorem distance_self (x : Point M o) : distance M o x x = 0 := by
  rcases x with _ | ⟨n,x⟩ <;> simp [distance]

theorem distance_comm (x y : Point M o) : distance M o x y = distance M o y x := by
  rcases x with _ | ⟨n,x⟩ <;> rcases y with _ | ⟨m,y⟩ <;> try rfl
  by_cases h : n = m
  · subst m; simp [distance,dist_comm]
  · simp [distance,h,Ne.symm h,add_comm]

theorem distance_triangle (x y z : Point M o) : distance M o x z ≤ distance M o x y + distance M o y z := by
  rcases x with _ | ⟨i,x⟩ <;> rcases y with _ | ⟨j,y⟩ <;> rcases z with _ | ⟨k,z⟩
  · simp [distance]
  · simp [distance]
  · simp only [distance]
    positivity
  · by_cases h : j = k
    · subst k
      simpa [distance,dist_comm,add_comm] using dist_triangle z.val y.val (o j)
    · simp only [distance,dite_eq_right h]
      have := dist_nonneg (x := y.val) (y := o j)
      linarith
  · simp [distance]
  · by_cases h : i = k
    · subst k
      simpa [distance,dist_comm] using dist_triangle x.val (o i) z.val
    · simp [distance,h]
  · by_cases h : i = j
    · subst j
      simpa [distance] using dist_triangle x.val y.val (o i)
    · simp only [distance,dite_eq_right h]
      have := dist_nonneg (x := y.val) (y := o j)
      linarith
  · by_cases hij : i = j
    · subst j
      by_cases hik : i = k
      · subst k
        simpa [distance] using dist_triangle x.val y.val z.val
      · simp only [distance,dite_true,dite_eq_right hik]
        have := dist_triangle x.val y.val (o i)
        linarith
    · by_cases hik : i = k
      · subst k
        simp only [distance,dite_true,dite_eq_right hij,dite_eq_right (Ne.symm hij)]
        have := dist_triangle x.val (o i) z.val
        have := dist_nonneg (x := y.val) (y := o j)
        rw [dist_comm (o i) z.val] at *
        linarith
      · by_cases hjk : j = k
        · subst k
          simp only [distance,dite_eq_right hij,dite_true]
          have := dist_triangle z.val y.val (o j)
          rw [dist_comm z.val y.val] at *
          linarith
        · simp only [distance,dite_eq_right hij,dite_eq_right hik,dite_eq_right hjk]
          have := dist_nonneg (x := y.val) (y := o j)
          linarith

theorem eq_of_distance_zero (x y : Point M o) (h : distance M o x y = 0) : x = y := by
  rcases x with _ | ⟨n,x⟩ <;> rcases y with _ | ⟨m,y⟩
  · rfl
  · exact False.elim (y.property (dist_eq_zero.mp h))
  · exact False.elim (x.property (dist_eq_zero.mp h))
  · by_cases hnm : n = m
    · subst m
      simp only [distance,dite_true] at h
      have he : x = y := Subtype.ext (dist_eq_zero.mp h)
      subst y
      rfl
    · simp only [distance,dite_eq_right hnm] at h
      have hx : 0 < dist x.val (o n) := dist_pos.mpr x.property
      have hy : 0 ≤ dist y.val (o m) := dist_nonneg
      linarith

instance : MetricSpace (Point M o) where
  dist := distance M o
  dist_self := distance_self M o
  dist_comm := distance_comm M o
  dist_triangle := distance_triangle M o
  eq_of_dist_eq_zero := eq_of_distance_zero M o _ _

def inclusion (n : ℕ) (x : M n) : Point M o :=
  if h : x = o n then none else some ⟨n,⟨x,h⟩⟩

def retraction (n : ℕ) : Point M o → M n
  | none => o n
  | some ⟨m,y⟩ => if h : m = n then h ▸ y.val else o n

omit [∀ n, MetricSpace (M n)] in
@[simp] theorem inclusion_base (n : ℕ) : inclusion M o n (o n) = base M o := by
  simp [inclusion,base]
  rfl

omit [∀ n, MetricSpace (M n)] in
@[simp] theorem retraction_base (n : ℕ) : retraction M o n (base M o) = o n := rfl

omit [∀ n, MetricSpace (M n)] in
@[simp] theorem retraction_inclusion (n : ℕ) (x : M n) :
    retraction M o n (inclusion M o n x) = x := by
  by_cases h : x = o n
  · simp [inclusion,h,retraction]
  · simp [inclusion,h,retraction]

omit [∀ n, MetricSpace (M n)] in
@[simp] theorem retraction_other {n m : ℕ} (h : n ≠ m) (x : M m) :
    retraction M o n (inclusion M o m x) = o n := by
  by_cases hx : x = o m <;> simp [inclusion,hx,retraction,Ne.symm h]

theorem inclusion_isometry (n : ℕ) : Isometry (inclusion M o n) := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  change distance M o _ _ = dist x y
  by_cases hx : x = o n <;> by_cases hy : y = o n <;> simp [inclusion,hx,hy,distance,dist_comm]

theorem retraction_lipschitz (n : ℕ) : LipschitzWith 1 (retraction M o n) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul]
  change dist _ _ ≤ distance M o x y
  rcases x with _ | ⟨i,x⟩ <;> rcases y with _ | ⟨j,y⟩
  · simp [distance,retraction]
  · by_cases h : j = n
    · subst j; simp [distance,retraction,dist_comm]
    · simp [distance,retraction,h]
  · by_cases h : i = n
    · subst i; simp [distance,retraction]
    · simp [distance,retraction,h]
  · by_cases hi : i = n
    · subst i
      by_cases hj : j = n
      · subst j; simp [distance,retraction]
      · simp [distance,retraction,hj,Ne.symm hj,dist_nonneg]
    · by_cases hj : j = n
      · subst j
        simp [distance,retraction,hi,dist_comm,dist_nonneg]
      · simp only [retraction,dite_eq_right hi,dite_eq_right hj,dist_self]
        exact @dist_nonneg (Point M o) _ (some ⟨i,x⟩) (some ⟨j,y⟩)

def retain (F : Finset ℕ) : Point M o → Point M o
  | none => none
  | some ⟨n,x⟩ => if n ∈ F then some ⟨n,x⟩ else none

omit [∀ n, MetricSpace (M n)] in
@[simp] theorem retain_base (F : Finset ℕ) : retain M o F (base M o) = base M o := rfl

omit [∀ n, MetricSpace (M n)] in
@[simp] theorem retain_inclusion (F : Finset ℕ) (n : ℕ) (x : M n) :
    retain M o F (inclusion M o n x) = if n ∈ F then inclusion M o n x else base M o := by
  by_cases hx : x = o n <;> by_cases hn : n ∈ F <;> simp [inclusion,hx,retain,hn,base] <;> rfl

theorem retain_lipschitz (F : Finset ℕ) : LipschitzWith 1 (retain M o F) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul]
  change distance M o _ _ ≤ distance M o x y
  rcases x with _ | ⟨i,x⟩ <;> rcases y with _ | ⟨j,y⟩
  · simp [retain,distance]
  · by_cases h : j ∈ F <;> simp [retain,h,distance,dist_nonneg]
  · by_cases h : i ∈ F <;> simp [retain,h,distance,dist_nonneg]
  · by_cases hi : i ∈ F <;> by_cases hj : j ∈ F
    · simp [retain,hi,hj]
    · have hn : i ≠ j := by rintro rfl; exact hj hi
      simp [retain,hi,hj,distance,hn,dist_nonneg]
    · have hn : i ≠ j := by rintro rfl; exact hi hj
      simp [retain,hi,hj,distance,hn,dist_nonneg]
    · have hh : 0 ≤ distance M o (some ⟨i,x⟩) (some ⟨j,y⟩) :=
        @dist_nonneg (Point M o) _ (some ⟨i,x⟩) (some ⟨j,y⟩)
      simpa [retain,hi,hj,distance] using hh

end DiscreteFree.MetricWedge
end

end

end OAI
