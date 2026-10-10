import OAI.NumberTheory.DukePrimeDegree.Geometry.RootCurveExtraction

namespace OAI

/-!
# Diagonal commutator curves and maximal root blocks

For a subgroup normalized by the split diagonal group, conjugating any
member by a small diagonal and taking a commutator produces a curve in
the subgroup. Its velocity has explicit entries. Root extraction then
forces conjugated coordinate projections to preserve every maximal
root block; connectedness gives global block preservation.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def diagonalCommutatorCurve {n : ℕ} (ell : Fin n → ℝ) (hsum : ∑ a, ell a = 0)
    (g : G n) (t : ℝ) : G n :=
  diagonalOneParameter ell hsum t * g * diagonalOneParameter ell hsum (-t) * g⁻¹

lemma diagonalCommutatorCurve_zero {n : ℕ}
    (ell : Fin n → ℝ) (hsum : ∑ a, ell a = 0) (g : G n) :
    diagonalCommutatorCurve ell hsum g 0 = 1 := by
  simp [diagonalCommutatorCurve, diagonalOneParameter_zero]

lemma diagonalCommutatorCurve_entry {n : ℕ}
    (ell : Fin n → ℝ) (hsum : ∑ a, ell a = 0) (g : G n) (t : ℝ) (a b : Fin n) :
    (diagonalCommutatorCurve ell hsum g t).val a b =
      ∑ k, Real.exp ((ell a - ell k) * t) * g.val a k * g⁻¹.val k b := by
  rw [diagonalCommutatorCurve, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [diagonal_conjugate_matrix_entry]

/-- The actual velocity of the diagonal commutator curve. -/
def diagonalCommutatorVelocity {n : ℕ} (ell : Fin n → ℝ) (g : G n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun a b => ∑ k, (ell a - ell k) * g.val a k * g⁻¹.val k b

lemma hasDerivAt_diagonalCommutatorCurve {n : ℕ}
    (ell : Fin n → ℝ) (hsum : ∑ a, ell a = 0) (g : G n) (a b : Fin n) :
    HasDerivAt (fun t => (diagonalCommutatorCurve ell hsum g t).val a b)
      (diagonalCommutatorVelocity ell g a b) 0 := by
  simp_rw [diagonalCommutatorCurve_entry]
  have hd : ∀ k ∈ (Finset.univ : Finset (Fin n)),
      HasDerivAt (fun t : ℝ => Real.exp ((ell a - ell k) * t) * g.val a k * g⁻¹.val k b)
        ((ell a - ell k) * g.val a k * g⁻¹.val k b) 0 := by
    intro k _
    convert (((hasDerivAt_id (0 : ℝ)).const_mul (ell a - ell k)).exp.mul_const
      (g.val a k)).mul_const (g⁻¹.val k b) using 1 <;> simp
  convert HasDerivAt.sum hd using 1
  · funext t
    simp only [Finset.sum_apply]
  · rfl

lemma hasMatrixVelocity_diagonalCommutatorCurve {n : ℕ}
    (ell : Fin n → ℝ) (hsum : ∑ a, ell a = 0) (g : G n) :
    HasMatrixVelocity (diagonalCommutatorCurve ell hsum g) (diagonalCommutatorVelocity ell g) :=
  hasMatrixVelocity_of_hasDerivAt _ (diagonalCommutatorCurve_zero ell hsum g) _
    (hasDerivAt_diagonalCommutatorCurve ell hsum g)

/-- Integral zero-sum weights detecting the k-th coordinate projection. -/
def coordinateProjectionWeights {n : ℕ} (k a : Fin n) : ℝ :=
  (n : ℝ) * (if a = k then 1 else 0) - 1

lemma coordinateProjectionWeights_sum {n : ℕ} (k : Fin n) :
    ∑ a, coordinateProjectionWeights k a = 0 := by
  simp [coordinateProjectionWeights, Finset.sum_sub_distrib]

lemma diagonalCommutatorVelocity_coordinate {n : ℕ} (k a b : Fin n)
    (hab : a ≠ b) (g : G n) :
    diagonalCommutatorVelocity (coordinateProjectionWeights k) g a b =
      -(n : ℝ) * (g.val a k * g⁻¹.val k b) := by
  let P : Fin n → ℝ := fun l => g.val a l * g⁻¹.val l b
  have hP : ∑ l, P l = 0 := by
    change (g.val * g⁻¹.val) a b = 0
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne hab]
  have he (l : Fin n) :
      (coordinateProjectionWeights k a - coordinateProjectionWeights k l) *
        g.val a l * g⁻¹.val l b =
      ((n : ℝ) * (if a = k then 1 else 0)) * P l -
        (n : ℝ) * (if l = k then P l else 0) := by
    dsimp [coordinateProjectionWeights, P]
    split_ifs <;> ring
  change (∑ l, (coordinateProjectionWeights k a - coordinateProjectionWeights k l) *
    g.val a l * g⁻¹.val l b) = _
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hP, mul_zero, zero_sub,
    ← Finset.mul_sum]
  simp [P]

/-- If every nonzero root found in L belongs to r, conjugated coordinate
projections have no entries between different r-blocks. -/
theorem projection_products_zero_of_maximal_roots {n : ℕ}
    (L : Subgroup (G n)) (hclosed : IsClosed (L : Set (G n)))
    (hnormal : ∀ (ell : Fin n → ℝ) (hsum : ∑ a, ell a = 0) (t : ℝ),
      ∀ g ∈ L, diagonalOneParameter ell hsum t * g * diagonalOneParameter ell hsum (-t) ∈ L)
    (r : Setoid (Fin n))
    (hmax : ∀ (a b : Fin n) (hab : a ≠ b) (c : ℝ), c ≠ 0 →
      Matrix.SpecialLinearGroup.transvection hab c ∈ L → r a b)
    (g : L) (a b : Fin n) (hab : ¬ r a b) (k : Fin n) :
    g.val.val a k * g.val⁻¹.val k b = 0 := by
  have hne : a ≠ b := by
    intro he
    subst b
    exact hab (r.refl a)
  let ell := coordinateProjectionWeights k
  have hsum := coordinateProjectionWeights_sum k
  let γ := diagonalCommutatorCurve ell hsum g.val
  have hγ (t : ℝ) : γ t ∈ L :=
    L.mul_mem (hnormal ell hsum t g.val g.property) (L.inv_mem g.property)
  have hroot := root_mem_of_matrix_velocity L hclosed hnormal γ hγ
    (diagonalCommutatorVelocity ell g.val)
    (hasMatrixVelocity_diagonalCommutatorCurve ell hsum g.val) a b hne
  have hvzero : diagonalCommutatorVelocity ell g.val a b = 0 := by
    by_contra hv
    exact hab (hmax a b hne _ hv hroot)
  rw [diagonalCommutatorVelocity_coordinate k a b hne g.val] at hvzero
  have hn : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fin.pos a))
  exact (mul_eq_zero.mp hvzero).resolve_left (neg_ne_zero.mpr hn)

/-- Root maximality makes the block-preserving subgroup open in the
actual homogeneous orbit group L, including when L is disconnected. -/
theorem blockIntersection_isOpen_of_maximal_roots {n : ℕ}
    (L : Subgroup (G n)) (hclosed : IsClosed (L : Set (G n)))
    (hnormal : ∀ (ell : Fin n → ℝ) (hsum : ∑ a, ell a = 0) (t : ℝ),
      ∀ g ∈ L, diagonalOneParameter ell hsum t * g * diagonalOneParameter ell hsum (-t) ∈ L)
    (r : Setoid (Fin n))
    (hmax : ∀ (a b : Fin n) (hab : a ≠ b) (c : ℝ), c ≠ 0 →
      Matrix.SpecialLinearGroup.transvection hab c ∈ L → r a b) :
    IsOpen (((blockMatrixGroup r).comap L.subtype : Subgroup L) : Set L) :=
  blockIntersection_isOpen_of_projection_products L r
    (projection_products_zero_of_maximal_roots L hclosed hnormal r hmax)

/-- A connected, closed subgroup normalized by the split diagonal group
preserves the partition given by its maximal root subgroups. This uses
only the explicit commutator curves and connectedness. -/
theorem connected_subgroup_le_blocks_of_maximal_roots {n : ℕ}
    (L : Subgroup (G n)) [PreconnectedSpace L]
    (hclosed : IsClosed (L : Set (G n)))
    (hnormal : ∀ (ell : Fin n → ℝ) (hsum : ∑ a, ell a = 0) (t : ℝ),
      ∀ g ∈ L, diagonalOneParameter ell hsum t * g * diagonalOneParameter ell hsum (-t) ∈ L)
    (r : Setoid (Fin n))
    (hmax : ∀ (a b : Fin n) (hab : a ≠ b) (c : ℝ), c ≠ 0 →
      Matrix.SpecialLinearGroup.transvection hab c ∈ L → r a b) :
    L ≤ blockMatrixGroup r :=
  connected_subgroup_le_blocks_of_projection_products L r
    (projection_products_zero_of_maximal_roots L hclosed hnormal r hmax)

end DukePrimeDegree

end

end OAI
