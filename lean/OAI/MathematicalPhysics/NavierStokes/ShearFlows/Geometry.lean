import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Affine

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

open Set MeasureTheory
open scoped BigOperators ContDiff Topology
namespace ShearFlows

def positiveMinimum (xs : List ℚ) : ℚ := xs.foldr min 1

theorem positiveMinimum_pos {xs : List ℚ} (hx : ∀ x ∈ xs, 0 < x) :
    0 < positiveMinimum xs := by
  induction xs with
  | nil => norm_num [positiveMinimum]
  | cons x xs ih =>
    exact lt_min (hx x (by simp)) (ih (fun y hy => hx y (by simp [hy])))

theorem positiveMinimum_le_of_mem {xs : List ℚ} {x : ℚ} (hx : x ∈ xs) :
    positiveMinimum xs ≤ x := by
  induction xs with
  | nil => simp at hx
  | cons y xs ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hx)

def boxGap (R S : RationalBox 2) : ℚ :=
  letI := neZeroTwo
  max (max (R.lower 0 - S.upper 0) (S.lower 0 - R.upper 0))
    (max (R.lower 1 - S.upper 1) (S.lower 1 - R.upper 1))

theorem boxGap_bounds (R S : RationalBox 2) (j : Fin 2) :
    R.lower j - S.upper j ≤ boxGap R S ∧ S.lower j - R.upper j ≤ boxGap R S := by
  fin_cases j
  · exact ⟨(le_max_left _ _).trans (le_max_left _ _),
      (le_max_right _ _).trans (le_max_left _ _)⟩
  · exact ⟨(le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩

theorem boxGap_pos_of_separated (R S : RationalBox 2)
    (hR : R.positive) (hS : S.positive)
    (hsep : PositivelySeparated R.carrier S.carrier) : 0 < boxGap R S := by
  by_contra hg
  have hg' : boxGap R S ≤ 0 := le_of_not_gt hg
  let X : Plane := fun j => max (R.lower j : ℝ) (S.lower j : ℝ)
  have hRS (j : Fin 2) : (R.lower j : ℝ) ≤ S.upper j ∧
      (S.lower j : ℝ) ≤ R.upper j := by
    have h := boxGap_bounds R S j
    constructor
    · exact_mod_cast (sub_nonpos.mp (h.1.trans hg'))
    · exact_mod_cast (sub_nonpos.mp (h.2.trans hg'))
  have hXR : X ∈ R.carrier := by
    intro j
    refine ⟨le_max_left _ _, max_le ?_ (hRS j).2⟩
    exact_mod_cast (hR j).le
  have hXS : X ∈ S.carrier := by
    intro j
    refine ⟨le_max_right _ _, max_le (hRS j).1 ?_⟩
    exact_mod_cast (hS j).le
  obtain ⟨ε, hε, hs⟩ := hsep
  have hbad := hs X hXR X hXS
  simp only [sub_self, norm_zero] at hbad
  exact (not_le_of_gt hε) hbad

def boxChartGap (A B : Fin 2 → ℚ) (R : RationalBox 2) : ℚ :=
  letI := neZeroTwo
  min (min (R.lower 0 - A 0) (B 0 - R.upper 0))
    (min (R.lower 1 - A 1) (B 1 - R.upper 1))

theorem boxChartGap_bounds (A B : Fin 2 → ℚ) (R : RationalBox 2) (j : Fin 2) :
    boxChartGap A B R ≤ R.lower j - A j ∧ boxChartGap A B R ≤ B j - R.upper j := by
  fin_cases j
  · exact ⟨(min_le_left _ _).trans (min_le_left _ _),
      (min_le_left _ _).trans (min_le_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans (min_le_right _ _)⟩

theorem boxChartGap_pos {A B : Fin 2 → ℚ} {R : RationalBox 2}
    (h : ∀ j, A j < R.lower j ∧ R.upper j < B j) : 0 < boxChartGap A B R := by
  exact lt_min (lt_min (sub_pos.mpr (h 0).1) (sub_pos.mpr (h 0).2))
    (lt_min (sub_pos.mpr (h 1).1) (sub_pos.mpr (h 1).2))

def collarRadius {n : ℕ} (A B : Fin 2 → ℚ) (R : Fin n → RationalBox 2) : ℚ :=
  min (positiveMinimum (List.ofFn (fun i => boxChartGap A B (R i))))
    (positiveMinimum (List.ofFn (fun i => positiveMinimum (List.ofFn
      (fun j => if i = j then 1 else boxGap (R i) (R j)))))) / 8

theorem collarRadius_pos {n : ℕ} {A B : Fin 2 → ℚ} {R : Fin n → RationalBox 2}
    (hc : ∀ i, 0 < boxChartGap A B (R i))
    (hg : ∀ i j, i ≠ j → 0 < boxGap (R i) (R j)) : 0 < collarRadius A B R := by
  apply div_pos _ (by norm_num : (0 : ℚ) < 8)
  apply lt_min
  · apply positiveMinimum_pos
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hc i
  · apply positiveMinimum_pos
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    apply positiveMinimum_pos
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    by_cases hij : i = j
    · simp [hij]
    · simpa [hij] using hg i j hij

theorem collarRadius_chart_bound {n : ℕ} (A B : Fin 2 → ℚ) (R : Fin n → RationalBox 2)
    (i : Fin n) : 8 * collarRadius A B R ≤ boxChartGap A B (R i) := by
  have h := positiveMinimum_le_of_mem (List.mem_ofFn.mpr ⟨i, rfl⟩ :
    boxChartGap A B (R i) ∈ List.ofFn (fun i => boxChartGap A B (R i)))
  have hmin := (min_le_left
    (positiveMinimum (List.ofFn (fun i => boxChartGap A B (R i))))
    (positiveMinimum (List.ofFn (fun i => positiveMinimum (List.ofFn
      (fun j => if i = j then 1 else boxGap (R i) (R j))))))).trans h
  dsimp [collarRadius]
  linarith

theorem collarRadius_gap_bound {n : ℕ} (A B : Fin 2 → ℚ) (R : Fin n → RationalBox 2)
    {i j : Fin n} (hij : i ≠ j) : 8 * collarRadius A B R ≤ boxGap (R i) (R j) := by
  let row := fun i => positiveMinimum (List.ofFn
    (fun j => if i = j then 1 else boxGap (R i) (R j)))
  have hrow := positiveMinimum_le_of_mem
    (List.mem_ofFn.mpr ⟨i, rfl⟩ : row i ∈ List.ofFn row)
  have hij' : boxGap (R i) (R j) ∈ List.ofFn
      (fun k => if i = k then 1 else boxGap (R i) (R k)) := by
    exact List.mem_ofFn.mpr ⟨j, by simp [hij]⟩
  have hcell : row i ≤ boxGap (R i) (R j) := positiveMinimum_le_of_mem hij'
  have hmin := (min_le_right
    (positiveMinimum (List.ofFn (fun i => boxChartGap A B (R i))))
    (positiveMinimum (List.ofFn row))).trans (hrow.trans hcell)
  dsimp [collarRadius, row] at *
  linarith

namespace RationalBox

def inflate {n : ℕ} (R : RationalBox n) (r : ℚ) : RationalBox n where
  lower j := R.lower j - r
  upper j := R.upper j + r

theorem subset_inflate {n : ℕ} (R : RationalBox n) {r : ℚ} (hr : 0 ≤ r) :
    R.carrier ⊆ (R.inflate r).carrier := by
  intro x hx j
  have hrr : (0 : ℝ) ≤ r := by exact_mod_cast hr
  obtain ⟨hlo, hhi⟩ := hx j
  constructor <;> dsimp [inflate] <;> push_cast <;> linarith

theorem inflate_mono {n : ℕ} (R : RationalBox n) {r s : ℚ} (hrs : r ≤ s) :
    (R.inflate r).carrier ⊆ (R.inflate s).carrier := by
  intro x hx j
  have hrs' : (r : ℝ) ≤ s := by exact_mod_cast hrs
  obtain ⟨hlo, hhi⟩ := hx j
  dsimp [inflate] at hlo hhi ⊢
  push_cast at hlo hhi ⊢
  constructor <;> linarith

end RationalBox

theorem collar_inside_chart {n : ℕ} {A B : Fin 2 → ℚ} {R : Fin n → RationalBox 2}
    (hr : 0 < collarRadius A B R) (i : Fin n) (j : Fin 2) :
    A j < ((R i).inflate (2 * collarRadius A B R)).lower j ∧
      ((R i).inflate (2 * collarRadius A B R)).upper j < B j := by
  have h := collarRadius_chart_bound A B R i
  have hb := boxChartGap_bounds A B (R i) j
  constructor <;> dsimp [RationalBox.inflate] <;> linarith

theorem collar_disjoint {n : ℕ} {A B : Fin 2 → ℚ} {R : Fin n → RationalBox 2}
    (hr : 0 < collarRadius A B R) {i j : Fin n} (hij : i ≠ j) :
    Disjoint (((R i).inflate (2 * collarRadius A B R)).carrier)
      (((R j).inflate (2 * collarRadius A B R)).carrier) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hr' : (0 : ℝ) < collarRadius A B R := by exact_mod_cast hr
  have hg : (8 : ℝ) * collarRadius A B R ≤ boxGap (R i) (R j) := by
    exact_mod_cast collarRadius_gap_bound A B R hij
  have hsmall (k : Fin 2) :
      ((R i).lower k : ℝ) - (R j).upper k ≤ 4 * collarRadius A B R ∧
      ((R j).lower k : ℝ) - (R i).upper k ≤ 4 * collarRadius A B R := by
    obtain ⟨hloi, hhii⟩ := hxi k
    obtain ⟨hloj, hhij⟩ := hxj k
    dsimp [RationalBox.inflate] at hloi hhii hloj hhij
    push_cast at hloi hhii hloj hhij
    constructor <;> linarith
  have hmax : (boxGap (R i) (R j) : ℝ) ≤ 4 * collarRadius A B R := by
    dsimp [boxGap]
    push_cast
    exact max_le (max_le (hsmall 0).1 (hsmall 0).2) (max_le (hsmall 1).1 (hsmall 1).2)
  linarith

end ShearFlows

end

end OAI
