import OAI.NumberTheory.DukePrimeDegree.Geometry.PluckerCovariance

namespace OAI

/-!
# From minor weights to an invariant subspace

In a genuine Grassmannian coordinate chart, the pivot rows of a frame
form the identity. A one-row replacement minor is then exactly the
corresponding graph coordinate. The single-weight minor conclusion
therefore forces the frame to intertwine the two diagonal operators.
-/

noncomputable section
open MeasureTheory Filter Matrix Set
open scoped BigOperators

namespace DukePrimeDegree

def replaceFramePivot {n k : ℕ} (p : Fin k ↪ Fin n) (j : Fin k) (i : Fin n) :
    Fin k ↪ Fin n := p.trans (Equiv.swap (p j) i).toEmbedding

lemma replaceFramePivot_self {n k : ℕ} (p : Fin k ↪ Fin n) (j : Fin k) (i : Fin n) :
    replaceFramePivot p j i j = i := by
  simp [replaceFramePivot]

lemma replaceFramePivot_other {n k : ℕ} (p : Fin k ↪ Fin n) (j : Fin k) (i : Fin n)
    (hi : i ∉ Set.range p) (u : Fin k) (hu : u ≠ j) :
    replaceFramePivot p j i u = p u := by
  apply Equiv.swap_apply_of_ne_of_ne
  · exact p.injective.ne hu
  · intro h
    exact hi ⟨u, h⟩

lemma frameMinor_replace_pivot {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ)
    (p : Fin k ↪ Fin n) (hp : B.submatrix p id = 1)
    (j : Fin k) (i : Fin n) (hi : i ∉ Set.range p) :
    frameMinor B (replaceFramePivot p j i) = B i j := by
  have he : B.submatrix (replaceFramePivot p j i) id =
      (1 : Matrix (Fin k) (Fin k) ℝ).updateRow j (B i) := by
    ext u v
    by_cases hu : u = j
    · subst u
      simp only [Matrix.submatrix_apply, id_eq, replaceFramePivot_self, Matrix.updateRow_self]
    · rw [Matrix.submatrix_apply, replaceFramePivot_other p j i hi u hu,
        Matrix.updateRow_ne hu]
      exact congrArg (fun A : Matrix (Fin k) (Fin k) ℝ => A u v) hp
  have hrow : (∑ u, (B i u) • (1 : Matrix (Fin k) (Fin k) ℝ) u) = B i := by
    ext v
    simp [Matrix.one_apply, Pi.smul_apply]
  change (B.submatrix (replaceFramePivot p j i) id).det = _
  rw [he]
  simpa only [hrow, Matrix.det_one, smul_eq_mul, mul_one] using
    Matrix.det_updateRow_sum (1 : Matrix (Fin k) (Fin k) ℝ) j (B i)

lemma replaced_pivot_weight_ne {n k : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (p : Fin k ↪ Fin n) (j : Fin k) (i : Fin n)
    (hi : i ∉ Set.range p) (hne : a i ≠ a (p j)) :
    (∏ u, a (replaceFramePivot p j i u)) ≠ ∏ u, a (p u) := by
  have he : (fun u => a (replaceFramePivot p j i u)) =
      Function.update (fun u => a (p u)) j (a i) := by
    funext u
    by_cases hu : u = j
    · subst u
      simp only [replaceFramePivot_self, Function.update_self]
    · simp only [replaceFramePivot_other p j i hi u hu, Function.update_of_ne hu]
  rw [he, Finset.prod_update_of_mem (Finset.mem_univ j), Finset.sdiff_singleton_eq_erase,
    ← Finset.mul_prod_erase Finset.univ (fun u => a (p u)) (Finset.mem_univ j)]
  exact fun h => hne (mul_right_cancel₀
    (Finset.prod_ne_zero_iff.mpr (fun u _ => ha (p u))) h)

/-- In a normalized frame chart, a graph coefficient joining unequal
diagonal weights must vanish. -/
theorem frame_entry_eq_zero_of_minor_weights {n k : ℕ}
    (B : Matrix (Fin n) (Fin k) ℝ) (p : Fin k ↪ Fin n)
    (hp : B.submatrix p id = 1)
    (a : Fin n → ℝ) (ha : ∀ i, a i ≠ 0)
    (hminor : ∀ q, (∏ u, a (q u)) ≠ ∏ u, a (p u) → frameMinor B q = 0)
    (i : Fin n) (j : Fin k) (hne : a i ≠ a (p j)) : B i j = 0 := by
  by_cases hi : i ∈ Set.range p
  · obtain ⟨u, rfl⟩ := hi
    have hu : u ≠ j := by
      intro h
      subst u
      exact hne rfl
    have he := congrArg (fun A : Matrix (Fin k) (Fin k) ℝ => A u j) hp
    simpa only [Matrix.submatrix_apply, id_eq, Matrix.one_apply_ne hu] using he
  · have hz := hminor (replaceFramePivot p j i)
      (replaced_pivot_weight_ne a ha p j i hi hne)
    simpa only [frameMinor_replace_pivot B p hp j i hi] using hz

/-- The frame intertwines the ambient diagonal operator and its pivot
restriction. Consequently its column subspace is invariant. -/
theorem diagonal_mul_frame_eq_frame_mul_diagonal {n k : ℕ}
    (B : Matrix (Fin n) (Fin k) ℝ) (p : Fin k ↪ Fin n)
    (hp : B.submatrix p id = 1)
    (a : Fin n → ℝ) (ha : ∀ i, a i ≠ 0)
    (hminor : ∀ q, (∏ u, a (q u)) ≠ ∏ u, a (p u) → frameMinor B q = 0) :
    Matrix.diagonal a * B = B * Matrix.diagonal (fun u => a (p u)) := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : a i = a (p j)
  · rw [h, mul_comm]
  · rw [frame_entry_eq_zero_of_minor_weights B p hp a ha hminor i j h,
      mul_zero, zero_mul]

/-- A finite invariant law of normalized frames is supported on frames
whose column spaces are invariant under the actual diagonal operator.
The frame covariance includes the genuine change of basis on its columns. -/
theorem ae_normalized_frame_diagonal_intertwining
    {Y : Type*} [MeasurableSpace Y] {n k : ℕ}
    (μ : Measure Y) [IsFiniteMeasure μ]
    (T : Y → Y) (hT : MeasurePreserving T μ μ)
    (B : Y → Matrix (Fin n) (Fin k) ℝ)
    (hB : ∀ i j, Measurable (fun x => B x i j))
    (p : Fin k ↪ Fin n) (hp : ∀ᵐ x ∂μ, (B x).submatrix p id = 1)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (R : Y → Matrix (Fin k) (Fin k) ℝ)
    (hR : ∀ᵐ x ∂μ, (R x).det ≠ 0)
    (hcov : ∀ᵐ x ∂μ, B (T x) = Matrix.diagonal a * B x * R x) :
    ∀ᵐ x ∂μ, Matrix.diagonal a * B x =
      B x * Matrix.diagonal (fun u => a (p u)) := by
  filter_upwards [hp, ae_frame_minors_have_one_diagonal_weight μ T hT B hB a ha R hR hcov]
    with x hx hweights
  apply diagonal_mul_frame_eq_frame_mul_diagonal (B x) p hx a
    (fun i => ne_of_gt (ha i))
  intro q hq
  have hpminor : frameMinor (B x) p = 1 := by
    change ((B x).submatrix p id).det = 1
    rw [hx, Matrix.det_one]
  exact (hweights q p hq).resolve_right (by rw [hpminor]; exact one_ne_zero)

end DukePrimeDegree

end

end OAI
