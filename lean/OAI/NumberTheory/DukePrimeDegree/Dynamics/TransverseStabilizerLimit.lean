import OAI.NumberTheory.DukePrimeDegree.Dynamics.BlockEliminationSchedule
import OAI.NumberTheory.DukePrimeDegree.Geometry.DiagonalCommutatorCurve
import OAI.NumberTheory.DukePrimeDegree.Dynamics.InvariantMeasureGroup

namespace OAI

/-!
# A transverse diagonal limit lies outside the stabilizer

The previously proved commutator identities give a global statement:
an element of L with nonzero diagonal preserves the maximal root blocks.
Consequently a nonidentity diagonal-conjugation limit with zero
within-block off-diagonal entries cannot belong to L. No additional
"limit outside L" assumption or connectedness assumption is used.
-/

noncomputable section
open Matrix Set Filter MeasureTheory
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma mem_blockMatrixGroup_of_cross_zero {n : ℕ} (r : Setoid (Fin n))
    (g : G n) (hzero : ∀ i j, ¬ r i j → g.val i j = 0) :
    g ∈ blockMatrixGroup r := by
  have hcomm := (commute_blockScalars_iff r g.val).mpr hzero
  intro c hc
  apply slMatrixConjugation_eq_self
  apply Commute.symm
  apply hcomm
  refine (mem_blockScalarAlgebra_iff r _).mpr ⟨by simp, ?_⟩
  intro i j hij
  simpa only [Matrix.diagonal_apply_eq] using hc i j hij

lemma cross_zero_of_mem_blockMatrixGroup {n : ℕ} (r : Setoid (Fin n))
    (g : G n) (hg : g ∈ blockMatrixGroup r) :
    ∀ i j, ¬ r i j → g.val i j = 0 := by
  apply (commute_blockScalars_iff r g.val).mp
  intro M hM
  exact ((slMatrixConjugation_eq_self_iff g M).mp
    (slMatrixConjugation_eq_self_of_mem_blockMatrixGroup r g hg M hM)).symm

/-- No smallness condition is required: using the nonzero diagonal
entry in each conjugated coordinate projection makes the inverse block
diagonal, hence the matrix itself block diagonal. -/
theorem mem_blocks_of_projection_products_and_nonzero_diagonal {n : ℕ}
    (r : Setoid (Fin n)) (g : G n)
    (hproducts : ∀ i j, ¬ r i j → ∀ k, g.val i k * g⁻¹.val k j = 0)
    (hdiag : ∀ i, g.val i i ≠ 0) : g ∈ blockMatrixGroup r := by
  have hinv : g⁻¹ ∈ blockMatrixGroup r := by
    apply mem_blockMatrixGroup_of_cross_zero r
    intro i j hij
    exact (mul_eq_zero.mp (hproducts i j hij i)).resolve_left (hdiag i)
  simpa only [inv_inv] using (blockMatrixGroup r).inv_mem hinv

theorem transverse_member_eq_one {n : ℕ}
    (r : Setoid (Fin n)) (g : G n)
    (hproducts : ∀ i j, ¬ r i j → ∀ k, g.val i k * g⁻¹.val k j = 0)
    (hdiag : ∀ i, g.val i i = 1)
    (hwithin : ∀ i j, i ≠ j → r i j → g.val i j = 0) : g = 1 := by
  have hblock := mem_blocks_of_projection_products_and_nonzero_diagonal r g hproducts
    (fun i => by rw [hdiag i]; exact one_ne_zero)
  have hcross := cross_zero_of_mem_blockMatrixGroup r g hblock
  apply Subtype.ext
  ext i j
  by_cases hij : i = j
  · subst j
    simpa only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] using hdiag i
  · rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne hij]
    by_cases hr : r i j
    · exact hwithin i j hij hr
    · exact hcross i j hr

/-- This endpoint uses the actual maximal-root property, already
available for the invariant-root equivalence relation. -/
theorem transverse_not_mem_of_maximal_roots {n : ℕ}
    (L : Subgroup (G n)) (hclosed : IsClosed (L : Set (G n)))
    (hnormal : ∀ (ell : Fin n → ℝ) (hsum : ∑ i, ell i = 0) (t : ℝ),
      ∀ g ∈ L, diagonalOneParameter ell hsum t * g * diagonalOneParameter ell hsum (-t) ∈ L)
    (r : Setoid (Fin n))
    (hmax : ∀ (i j : Fin n) (hij : i ≠ j) (c : ℝ), c ≠ 0 →
      Matrix.SpecialLinearGroup.transvection hij c ∈ L → r i j)
    (g : G n) (hne : g ≠ 1) (hdiag : ∀ i, g.val i i = 1)
    (hwithin : ∀ i j, i ≠ j → r i j → g.val i j = 0) : g ∉ L := by
  intro hg
  apply hne
  exact transverse_member_eq_one r g
    (projection_products_zero_of_maximal_roots L hclosed hnormal r hmax ⟨g, hg⟩)
    hdiag hwithin

/-- Diagonal rescaling preserves every cleared within-block entry and
leaves the diagonal unchanged, including for diverging rescaling times. -/
theorem diagonal_transverse_limit_entries {n : ℕ}
    (r : Setoid (Fin n)) (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (hzero : ∀ᶠ k in atTop, ∀ i j, i ≠ j → r i j → (g k).val i j = 0)
    (ell : Fin n → ℝ) (hsum : ∑ i, ell i = 0) (t : ℕ → ℝ)
    (h : G n)
    (hlim : Tendsto (fun k => diagonalOneParameter ell hsum (t k) * g k *
      diagonalOneParameter ell hsum (-t k)) atTop (𝓝 h)) :
    (∀ i, h.val i i = 1) ∧ (∀ i j, i ≠ j → r i j → h.val i j = 0) := by
  have hc (i j : Fin n) : Continuous (fun a : G n => a.val i j) := by fun_prop
  constructor
  · intro i
    have hh := (hc i i).continuousAt.tendsto.comp hlim
    have he := (hc i i).continuousAt.tendsto.comp hg
    have he' : Tendsto (fun k => (diagonalOneParameter ell hsum (t k) * g k *
        diagonalOneParameter ell hsum (-t k)).val i i) atTop (𝓝 1) := by
      simpa only [Function.comp_def, diagonal_conjugate_matrix_entry, sub_self, zero_mul, Real.exp_zero,
        one_mul, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] using he
    exact tendsto_nhds_unique hh he'
  · intro i j hij hr
    have hh := (hc i j).continuousAt.tendsto.comp hlim
    have he : ∀ᶠ k in atTop, (diagonalOneParameter ell hsum (t k) * g k *
        diagonalOneParameter ell hsum (-t k)).val i j = 0 := by
      filter_upwards [hzero] with k hk
      rw [diagonal_conjugate_matrix_entry, hk i j hij hr, mul_zero]
    exact tendsto_nhds_unique hh (tendsto_const_nhds.congr' (he.mono fun k hk => hk.symm))

theorem diagonal_transverse_limit_not_mem {n : ℕ}
    (L : Subgroup (G n)) (hclosed : IsClosed (L : Set (G n)))
    (hnormal : ∀ (ell : Fin n → ℝ) (hsum : ∑ i, ell i = 0) (t : ℝ),
      ∀ g ∈ L, diagonalOneParameter ell hsum t * g * diagonalOneParameter ell hsum (-t) ∈ L)
    (r : Setoid (Fin n))
    (hmax : ∀ (i j : Fin n) (hij : i ≠ j) (c : ℝ), c ≠ 0 →
      Matrix.SpecialLinearGroup.transvection hij c ∈ L → r i j)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (hzero : ∀ᶠ k in atTop, ∀ i j, i ≠ j → r i j → (g k).val i j = 0)
    (ell : Fin n → ℝ) (hsum : ∑ i, ell i = 0) (t : ℕ → ℝ)
    (h : G n) (hne : h ≠ 1)
    (hlim : Tendsto (fun k => diagonalOneParameter ell hsum (t k) * g k *
      diagonalOneParameter ell hsum (-t k)) atTop (𝓝 h)) : h ∉ L := by
  obtain ⟨hd, hz⟩ := diagonal_transverse_limit_entries r g hg hzero ell hsum t h hlim
  exact transverse_not_mem_of_maximal_roots L hclosed hnormal r hmax h hne hd hz

/-- Specialization to the actual finite-measure stabilizer. All subgroup
closedness, normalization, and maximal-root hypotheses are proved here
from A-invariance and the actual invariant-root relation. -/
theorem actual_invariant_subgroup_transverse_not_mem
    (d : ℕ) (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (r : Setoid (Fin (d + 1)))
    (hr : ∀ i j, r i j ↔ rootInvarianceRelation μ i j)
    (g : G (d + 1)) (hne : g ≠ 1) (hdiag : ∀ i, g.val i i = 1)
    (hwithin : ∀ i j, i ≠ j → r i j → g.val i j = 0) :
    g ∉ invariantRightSubgroup μ := by
  let L := invariantRightSubgroup μ
  have hdiagmem (ell : Fin (d + 1) → ℝ) (hsum : ∑ i, ell i = 0) (t : ℝ) :
      diagonalOneParameter ell hsum t ∈ L := by
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hnormal : ∀ (ell : Fin (d + 1) → ℝ) (hsum : ∑ i, ell i = 0) (t : ℝ),
      ∀ g ∈ L, diagonalOneParameter ell hsum t * g *
        diagonalOneParameter ell hsum (-t) ∈ L := by
    intro ell hsum t g hg
    exact L.mul_mem (L.mul_mem (hdiagmem ell hsum t) hg) (hdiagmem ell hsum (-t))
  have hmax : ∀ (i j : Fin (d + 1)) (hij : i ≠ j) (c : ℝ), c ≠ 0 →
      Matrix.SpecialLinearGroup.transvection hij c ∈ L → r i j := by
    intro i j hij c hc hg
    exact (hr i j).mpr (Or.inr ⟨hij,
      root_mem_of_nonzero_parameter L hA hij hc hg⟩)
  exact transverse_not_mem_of_maximal_roots L (isClosed_invariantRightSubgroup μ)
    hnormal r hmax g hne hdiag hwithin

end DukePrimeDegree

end

end OAI
