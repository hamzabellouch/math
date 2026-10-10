import OAI.Combinatorics.CliqueFree.Numerical

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

def mass (w : V → ℝ) (A : Finset V) : ℝ := ∑ v ∈ A, w v

noncomputable def neighbors (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact univ.filter (G.Adj v)

@[simp] lemma mem_neighbors (G : SimpleGraph V) (u v : V) :
    v ∈ neighbors G u ↔ G.Adj u v := by
  classical
  simp [neighbors]

noncomputable def crossMass (G : SimpleGraph V) (w : V → ℝ) (A B : Finset V) : ℝ := by
  classical
  exact ∑ u ∈ A, ∑ v ∈ B, if G.Adj u v then w u * w v else 0

/-- Unordered edge mass, written as half the directed edge mass. -/
noncomputable def edgeMass (G : SimpleGraph V) (w : V → ℝ) : ℝ :=
  crossMass G w univ univ / 2

noncomputable def neighborMass (G : SimpleGraph V) (w : V → ℝ) (u : V) : ℝ :=
  mass w (neighbors G u)

noncomputable def commonMass (G : SimpleGraph V) (w : V → ℝ) (u v : V) : ℝ := by
  classical
  exact mass w (neighbors G u ∩ neighbors G v)

/-- Twice the triangle mass in the weighted neighborhood of u. -/
noncomputable def triangleAt (G : SimpleGraph V) (w : V → ℝ) (u : V) : ℝ :=
  ∑ v ∈ neighbors G u, w v * commonMass G w u v

/-- Unordered triangle mass, written as one sixth of the ordered triangle mass. -/
noncomputable def triangleMass (G : SimpleGraph V) (w : V → ℝ) : ℝ :=
  (∑ u, w u * triangleAt G w u) / 6

/-- The growth function `g_x`, including its zero convention. Only nonnegative `s` are used. -/
noncomputable def growth (x s : ℝ) : ℝ := s * (x + max 0 (Real.log (1 / s)))

/-- The full cross-mass property; sets may overlap. -/
def CrossBound (G : SimpleGraph V) (w : V → ℝ) (C : ℝ) : Prop :=
  ∀ (x : ℝ), 1 ≤ x → ∀ (A B : Finset V),
    mass w A ≤ Real.exp x → mass w B ≤ Real.exp x →
      crossMass G w A B ≤ C * growth x (mass w A)

omit [Fintype V] in
lemma mass_nonneg {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (A : Finset V) :
    0 ≤ mass w A := sum_nonneg fun v _ ↦ hw v

omit [Fintype V] in
lemma mass_mono {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {A B : Finset V} (hAB : A ⊆ B) :
    mass w A ≤ mass w B := sum_le_sum_of_subset_of_nonneg hAB (fun v _ _ ↦ hw v)

omit [Fintype V] in
lemma crossMass_symm (G : SimpleGraph V) (w : V → ℝ) (A B : Finset V) :
    crossMass G w A B = crossMass G w B A := by
  classical
  unfold crossMass
  rw [sum_comm]
  simp_rw [G.adj_comm, mul_comm]

omit [Fintype V] in
lemma crossMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (A B : Finset V) : 0 ≤ crossMass G w A B := by
  classical
  exact sum_nonneg fun u _ ↦ sum_nonneg fun v _ ↦ by
    split_ifs
    · exact mul_nonneg (hw u) (hw v)
    · exact le_rfl

omit [Fintype V] in
lemma crossMass_le_product (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (A B : Finset V) : crossMass G w A B ≤ mass w A * mass w B := by
  classical
  unfold crossMass mass
  rw [sum_mul_sum]
  exact sum_le_sum fun u _ ↦ sum_le_sum fun v _ ↦ by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hw u) (hw v)

lemma crossMass_factor (G : SimpleGraph V) (w : V → ℝ) (A B : Finset V) :
    crossMass G w A B = ∑ u ∈ A, w u * mass w (B ∩ neighbors G u) := by
  classical
  unfold crossMass mass
  apply sum_congr rfl
  intro u _
  rw [← filter_mem_eq_inter]
  simp only [sum_filter, mem_neighbors, mul_sum, mul_ite, mul_zero]

lemma commonMass_comm (G : SimpleGraph V) (w : V → ℝ) (u v : V) :
    commonMass G w u v = commonMass G w v u := by
  classical
  simp [commonMass, inter_comm]

lemma commonMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (u v : V) :
    0 ≤ commonMass G w u v := mass_nonneg hw _

lemma neighborMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (u : V) :
    0 ≤ neighborMass G w u := mass_nonneg hw _

lemma commonMass_le_neighborMass (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (u v : V) : commonMass G w u v ≤ neighborMass G w u := by
  classical
  exact mass_mono hw inter_subset_left

lemma edgeMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) :
    0 ≤ edgeMass G w := div_nonneg (crossMass_nonneg G hw _ _) (by norm_num)

lemma triangleAt_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (u : V) :
    0 ≤ triangleAt G w u :=
  sum_nonneg fun v _ ↦ mul_nonneg (hw v) (commonMass_nonneg G hw u v)

lemma triangleMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) :
    0 ≤ triangleMass G w := div_nonneg
      (sum_nonneg fun u _ ↦ mul_nonneg (hw u) (triangleAt_nonneg G hw u)) (by norm_num)

lemma edgeMass_eq_sum (G : SimpleGraph V) (w : V → ℝ) :
    2 * edgeMass G w = ∑ u, w u * neighborMass G w u := by
  classical
  rw [edgeMass, crossMass_factor]
  simp only [univ_inter, neighborMass]
  ring

lemma triangleMass_eq_sum (G : SimpleGraph V) (w : V → ℝ) :
    6 * triangleMass G w = ∑ u, w u * triangleAt G w u := by
  unfold triangleMass
  ring

lemma triangleAt_le (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {L : ℝ} (hL : ∀ u, neighborMass G w u ≤ L) (u : V) :
    triangleAt G w u ≤ L * neighborMass G w u := by
  calc
    _ ≤ ∑ v ∈ neighbors G u, w v * L := sum_le_sum fun v _ ↦
      mul_le_mul_of_nonneg_left ((commonMass_le_neighborMass G hw u v).trans (hL u)) (hw v)
    _ = _ := by rw [← sum_mul]; exact mul_comm _ _

lemma triangleMass_le_of_neighborMass (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) {L : ℝ} (hL : ∀ u, neighborMass G w u ≤ L) :
    triangleMass G w ≤ L / 3 * edgeMass G w := by
  have h : 6 * triangleMass G w ≤ L * (2 * edgeMass G w) := by
    rw [triangleMass_eq_sum, edgeMass_eq_sum, mul_sum]
    exact sum_le_sum fun u _ ↦ by
      have := mul_le_mul_of_nonneg_left (triangleAt_le G hw hL u) (hw u)
      nlinarith
  linarith

lemma neighborMass_ge_of_commonMass (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) {τ : ℝ} (hc : ∀ u v, G.Adj u v → τ ≤ commonMass G w u v)
    {u : V} (hu : (neighbors G u).Nonempty) : τ ≤ neighborMass G w u := by
  rcases hu with ⟨v, hv⟩
  exact (hc u v (mem_neighbors G u v |>.1 hv)).trans (commonMass_le_neighborMass G hw u v)

lemma triangleAt_ge_of_commonMass (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) {τ : ℝ} (hc : ∀ u v, G.Adj u v → τ ≤ commonMass G w u v)
    (u : V) : τ * neighborMass G w u ≤ triangleAt G w u := by
  calc
    _ = ∑ v ∈ neighbors G u, w v * τ := by rw [← sum_mul]; exact mul_comm _ _
    _ ≤ _ := sum_le_sum fun v hv ↦ mul_le_mul_of_nonneg_left
      (hc u v (mem_neighbors G u v |>.1 hv)) (hw v)

lemma commonMass_eq_sum (G : SimpleGraph V) (w : V → ℝ) (u v : V) :
    commonMass G w u v = ∑ z ∈ neighbors G u, if G.Adj v z then w z else 0 := by
  classical
  unfold commonMass mass
  rw [← filter_mem_eq_inter, sum_filter]
  simp only [mem_neighbors]

lemma crossMass_all_right (G : SimpleGraph V) (w : V → ℝ) (A : Finset V) :
    crossMass G w A univ = ∑ u ∈ A, w u * neighborMass G w u := by
  classical
  rw [crossMass_factor]
  simp [neighborMass]

lemma crossMass_all_left (G : SimpleGraph V) (w : V → ℝ) (A : Finset V) :
    crossMass G w univ A = ∑ u ∈ A, w u * neighborMass G w u := by
  rw [crossMass_symm, crossMass_all_right]

lemma crossMass_neighbors (G : SimpleGraph V) (w : V → ℝ)
    (A : Finset V) (v : V) :
    crossMass G w A (neighbors G v) = ∑ u ∈ A, w u * commonMass G w u v := by
  rw [crossMass_factor]
  simp only [commonMass, inter_comm]

end CliqueFreeIndependence.WeightedGraph

end

end OAI
