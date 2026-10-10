import OAI.Combinatorics.FiniteCircle.Partitions

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

noncomputable def histogram {X Y : Type*} (label : X → Y) (xs : List X) (y : Y) : ℝ := by
  classical
  exact (xs.map (fun x => if label x = y then (1 : ℝ) else 0)).sum

@[simp] theorem histogram_nil {X Y : Type*} (label : X → Y) (y : Y) :
    histogram label [] y = 0 := by simp [histogram]

@[simp] theorem histogram_cons {X Y : Type*} [DecidableEq Y] (label : X → Y) (x : X) (xs : List X) (y : Y) :
    histogram label (x :: xs) y = (if label x = y then 1 else 0) + histogram label xs y := by
  classical
  simp [histogram]

@[simp] theorem histogram_append {X Y : Type*} (label : X → Y) (xs ys : List X) (y : Y) :
    histogram label (xs ++ ys) y = histogram label xs y + histogram label ys y := by
  simp [histogram]

theorem histogram_nonneg {X Y : Type*} (label : X → Y) (xs : List X) (y : Y) :
    0 ≤ histogram label xs y := by
  classical
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [histogram_cons]
    split <;> linarith

theorem histogram_mass {X Y : Type*} [Fintype Y] (label : X → Y) (xs : List X) :
    ∑ y, histogram label xs y = xs.length := by
  classical
  induction xs with
  | nil => simp
  | cons x xs ih => simp [histogram_cons, Finset.sum_add_distrib, ih, Nat.cast_add, add_comm]

theorem histogram_eq_zero {X Y : Type*} (label : X → Y) (xs : List X) (y : Y)
    (h : ∀ x ∈ xs, label x ≠ y) : histogram label xs y = 0 := by
  classical
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [histogram_cons, ite_eq_right (h x (by simp)), zero_add]
    exact ih (fun z hz => h z (by simp [hz]))

noncomputable def histDist {X Y : Type*} [Fintype Y] (label : X → Y) (xs ys : List X) : ℝ :=
  ∑ y, |histogram label xs y - histogram label ys y|

@[simp] theorem histDist_self {X Y : Type*} [Fintype Y] (label : X → Y) (xs : List X) :
    histDist label xs xs = 0 := by simp [histDist]

theorem histDist_nonneg {X Y : Type*} [Fintype Y] (label : X → Y) (xs ys : List X) :
    0 ≤ histDist label xs ys := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem histDist_symm {X Y : Type*} [Fintype Y] (label : X → Y) (xs ys : List X) :
    histDist label xs ys = histDist label ys xs := by
  unfold histDist
  simp only [abs_sub_comm]

theorem histDist_triangle {X Y : Type*} [Fintype Y] (label : X → Y) (xs ys zs : List X) :
    histDist label xs zs ≤ histDist label xs ys + histDist label ys zs := by
  unfold histDist
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun _ _ => abs_sub_le _ _ _)

theorem histDist_le_mass {X Y : Type*} [Fintype Y] (label : X → Y) (xs ys : List X) :
    histDist label xs ys ≤ xs.length + ys.length := by
  calc
    _ ≤ ∑ y, (histogram label xs y + histogram label ys y) := by
      apply Finset.sum_le_sum
      intro y _
      exact abs_sub_le_iff.mpr ⟨by linarith [histogram_nonneg label ys y],
        by linarith [histogram_nonneg label xs y]⟩
    _ = _ := by rw [Finset.sum_add_distrib, histogram_mass, histogram_mass]

theorem histDist_disjoint {X Y : Type*} [Fintype Y] (label : X → Y) (xs ys : List X)
    (h : ∀ x ∈ xs, ∀ y ∈ ys, label x ≠ label y) :
    histDist label xs ys = xs.length + ys.length := by
  classical
  calc
    _ = ∑ y, (histogram label xs y + histogram label ys y) := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases he : ∃ x ∈ xs, label x = y
      · obtain ⟨x, hx, rfl⟩ := he
        rw [histogram_eq_zero label ys _ (fun z hz => Ne.symm (h x hx z hz))]
        simp [abs_of_nonneg (histogram_nonneg label xs (label x))]
      · rw [histogram_eq_zero label xs _ (fun x hx heq => he ⟨x, hx, heq⟩)]
        simp [abs_of_nonneg (histogram_nonneg label ys y)]
    _ = _ := by rw [Finset.sum_add_distrib, histogram_mass, histogram_mass]

theorem histDist_append_le {X Y : Type*} [Fintype Y] (label : X → Y)
    (xs ys us vs : List X) :
    histDist label (xs ++ us) (ys ++ vs) ≤ histDist label xs ys + histDist label us vs := by
  unfold histDist
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro y _
  simp only [histogram_append]
  convert abs_add_le (histogram label xs y - histogram label ys y)
    (histogram label us y - histogram label vs y) using 1
  congr 1
  ring

@[simp] theorem histDist_singleton {X Y : Type*} [Fintype Y] [DecidableEq Y] (label : X → Y) (x y : X) :
    histDist label [x] [y] = if label x = label y then 0 else 2 := by
  classical
  by_cases h : label x = label y
  · rw [ite_eq_left h]
    unfold histDist
    apply Finset.sum_eq_zero
    intro z _
    by_cases hz : label y = z <;> simp [histogram, h, hz]
  · rw [ite_eq_right h, histDist_disjoint label [x] [y] (by simpa using h)]
    norm_num

theorem histDist_cons_le {X Y : Type*} [Fintype Y] [DecidableEq Y] (label : X → Y) (x y : X) (xs ys : List X) :
    histDist label (x :: xs) (y :: ys) ≤
      (if label x = label y then 0 else 2) + histDist label xs ys := by
  classical
  simpa only [List.singleton_append, histDist_singleton] using histDist_append_le label [x] [y] xs ys

theorem histogram_mono {X Y : Type*} (label : X → Y) {xs ys : List X} (h : xs <+ ys) (y : Y) :
    histogram label xs y ≤ histogram label ys y := by
  classical
  induction h with
  | slnil => exact le_rfl
  | cons a h ih =>
    rw [histogram_cons]
    split <;> linarith
  | cons_cons a h ih =>
    rw [histogram_cons, histogram_cons]
    by_cases ha : label a = y <;> simp only [ha, ite_true, ite_false] <;> linarith

theorem histDist_sublist {X Y : Type*} [Fintype Y] (label : X → Y)
    {xs ys : List X} (h : xs <+ ys) : histDist label xs ys = ys.length - xs.length := by
  unfold histDist
  simp only [abs_of_nonpos (sub_nonpos.mpr (histogram_mono label h _))]
  simp only [neg_sub, Finset.sum_sub_distrib, histogram_mass]

theorem histDist_common_sublist_le {X Y : Type*} [Fintype Y] (label : X → Y)
    {xs ys zs : List X} (hx : zs <+ xs) (hy : zs <+ ys) :
    histDist label xs ys ≤ xs.length + ys.length - 2 * zs.length := by
  calc
    _ ≤ histDist label xs zs + histDist label zs ys := histDist_triangle _ _ _ _
    _ = _ := by rw [histDist_symm label xs, histDist_sublist label hx, histDist_sublist label hy]; ring

theorem histDist_ofFn_le {X Y : Type*} [Fintype Y] [DecidableEq Y]
    (label : X → Y) {s : ℕ} (f g : Fin s → X) :
    histDist label (List.ofFn f) (List.ofFn g) ≤
      2 * ∑ i, (if label (f i) = label (g i) then (0 : ℝ) else 1) := by
  induction s with
  | zero => simp [histDist]
  | succ s ih =>
    rw [List.ofFn_succ, List.ofFn_succ, Fin.sum_univ_succ, mul_add]
    refine (histDist_cons_le _ _ _ _ _).trans (add_le_add ?_ (ih _ _))
    split <;> norm_num

noncomputable def histMap {X Ω Y : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (label : Ω → X → Y) (xs : List X) (i : Ω × Y) : ℝ :=
  μ.weight i.1 * histogram (label i.1) xs i.2

theorem histMap_distance {X Ω Y : Type*} [Fintype Ω] [Fintype Y]
    (μ : FiniteLaw Ω) (label : Ω → X → Y) (xs ys : List X) :
    ∑ i, |histMap μ label xs i - histMap μ label ys i| =
      μ.expect (fun ω => histDist (label ω) xs ys) := by
  simp only [histMap, ← mul_sub, abs_mul, abs_of_nonneg (μ.nonneg _),
    Fintype.sum_prod_type, FiniteLaw.expect, histDist, Finset.mul_sum]

theorem expect_histDist_ofFn_le {X Ω Y : Type*} [Fintype Ω] [Fintype Y]
    (μ : FiniteLaw Ω) (label : Ω → X → Y) {s : ℕ} (f g : Fin s → X)
    (p : ℝ) (hp : ∀ i, μ.event (fun ω => label ω (f i) ≠ label ω (g i)) ≤ p) :
    μ.expect (fun ω => histDist (label ω) (List.ofFn f) (List.ofFn g)) ≤ 2 * s * p := by
  classical
  calc
    _ ≤ μ.expect (fun ω => 2 * ∑ i, if label ω (f i) = label ω (g i) then 0 else 1) :=
      μ.expect_mono (fun _ => histDist_ofFn_le _ _ _)
    _ = 2 * ∑ i, μ.event (fun ω => label ω (f i) ≠ label ω (g i)) := by
      rw [μ.expect_smul, μ.expect_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [FiniteLaw.event_eq_expect]
      congr 1
      funext ω
      split <;> simp_all
    _ ≤ 2 * ∑ _i : Fin s, p := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hp i)) (by norm_num)
    _ = _ := by simp; ring

theorem expect_histDist_ofFn_ge {X Ω Y : Type*} [Fintype Ω] [Fintype Y]
    (μ : FiniteLaw Ω) (label : Ω → X → Y) {s : ℕ} (f g : Fin s → X)
    (p : ℝ) (hp : ∀ i j, μ.event (fun ω => label ω (f i) = label ω (g j)) ≤ p)
    (hsp : (s : ℝ)^2 * p ≤ 1 / 2) :
    (s : ℝ) ≤ μ.expect (fun ω => histDist (label ω) (List.ofFn f) (List.ofFn g)) := by
  classical
  let Collision := fun ω => ∃ ij : Fin s × Fin s, label ω (f ij.1) = label ω (g ij.2)
  have hc : μ.event Collision ≤ 1 / 2 := by
    calc
      _ ≤ ∑ ij : Fin s × Fin s, μ.event (fun ω => label ω (f ij.1) = label ω (g ij.2)) :=
        μ.event_exists_le_sum _
      _ ≤ ∑ _ij : Fin s × Fin s, p := Finset.sum_le_sum (fun ij _ => hp ij.1 ij.2)
      _ = (s : ℝ)^2 * p := by simp [sq, mul_assoc]
      _ ≤ _ := hsp
  have hn : 1 / 2 ≤ μ.event (fun ω => ¬Collision ω) := by rw [μ.event_compl]; linarith
  have hd : 2 * s * μ.event (fun ω => ¬Collision ω) ≤
      μ.expect (fun ω => histDist (label ω) (List.ofFn f) (List.ofFn g)) := by
    rw [FiniteLaw.event_eq_expect, ← μ.expect_smul]
    apply μ.expect_mono
    intro ω
    by_cases h : Collision ω
    · simp only [ite_eq_right (not_not_intro h), mul_zero]
      exact histDist_nonneg _ _ _
    · rw [ite_eq_left h, mul_one]
      have hdis : ∀ x ∈ List.ofFn f, ∀ y ∈ List.ofFn g, label ω x ≠ label ω y := by
        intro x hx y hy heq
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
        exact h ⟨(i,j), heq⟩
      rw [histDist_disjoint _ _ _ hdis]
      simp only [List.length_ofFn]
      linarith
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  nlinarith

end FiniteCircle

end OAI
