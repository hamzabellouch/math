import OAI.Geometry.CylinderCovering.Nilpotent.SmoothRateDefinitions
import OAI.Geometry.CylinderCovering.Nilpotent.Grid

namespace OAI

noncomputable section
open Set Metric

namespace CylinderCovering.NilpotentRate

lemma integerVector_antilipschitz : AntilipschitzWith 1 integerVector := by
  apply AntilipschitzWith.of_le_mul_dist
  intro i j
  rw [NNReal.coe_one, one_mul, Prod.dist_eq, Int.dist_eq, Int.dist_eq,
    dist_eq_norm]
  apply max_le
  · simpa [integerVector, RuledApproximation.vec2, Real.norm_eq_abs] using
      (PiLp.norm_apply_le (integerVector i - integerVector j) (0 : Fin 2))
  · simpa [integerVector, RuledApproximation.vec2, Real.norm_eq_abs] using
      (PiLp.norm_apply_le (integerVector i - integerVector j) (1 : Fin 2))

lemma scaled_integerVector_antilipschitz (Q : Plane ≃ₗᵢ[ℝ] Plane)
    {τ : ℝ} (hτ : 0 < τ) :
    AntilipschitzWith (⟨τ, hτ.le⟩ : NNReal)⁻¹
      (fun j : Index => τ • Q (integerVector j)) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro i j
  calc
    dist i j ≤ dist (integerVector i) (integerVector j) := by
      simpa using integerVector_antilipschitz.le_mul_dist i j
    _ = ↑((⟨τ, hτ.le⟩ : NNReal)⁻¹) *
        dist (τ • Q (integerVector i)) (τ • Q (integerVector j)) := by
      rw [dist_smul₀, Q.dist_map, Real.norm_eq_abs, abs_of_pos hτ]
      change dist (integerVector i) (integerVector j) =
        τ⁻¹ * (τ * dist (integerVector i) (integerVector j))
      simp [hτ.ne']

theorem finite_lattice_neighborhood (Q : Plane ≃ₗᵢ[ℝ] Plane)
    {τ : ℝ} (hτ : 0 < τ) {S : Set Plane}
    (hS : Bornology.IsBounded S) (hne : S.Nonempty) (R : ℝ) :
    {j : Index | infDist (τ • Q (integerVector j)) S ≤ R}.Finite := by
  have hb : Bornology.IsBounded
      ((fun j : Index => τ • Q (integerVector j)) ⁻¹' thickening (R + 1) S) :=
    (scaled_integerVector_antilipschitz Q hτ).isBounded_preimage hS.thickening
  apply hb.isCompact_closure.finite_of_discrete.subset
  intro j hj
  apply subset_closure
  exact (mem_thickening_iff_infDist_lt hne).mpr (lt_of_le_of_lt hj (by linarith))

theorem finite_fineCenter_neighborhood (Q : Plane ≃ₗᵢ[ℝ] Plane)
    {δ : ℝ} (hδ : 0 < δ) {S : Set Plane}
    (hS : Bornology.IsBounded S) (hne : S.Nonempty) (R : ℝ) :
    {j : Index | infDist (fineCenter δ Q j) S ≤ R}.Finite :=
  finite_lattice_neighborhood Q (sq_pos_of_pos hδ) hS hne R

theorem finite_coarseIndices {δ : ℝ} (hδ : 0 < δ) {D : Set Plane}
    (hD : Bornology.IsBounded D) : (coarseIndices δ D).Finite := by
  obtain ⟨B, hB⟩ := hD.exists_norm_le
  have hcoords : ∀ x ∈ D, |x 0| ≤ B ∧ |x 1| ≤ B := by
    intro x hx
    constructor
    · have hi : |x 0| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x (0 : Fin 2)
      exact hi.trans (hB x hx)
    · have hi : |x 1| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x (1 : Fin 2)
      exact hi.trans (hB x hx)
  apply (NilpotentGrid.coarseIndices δ B D).finite_toSet.subset
  intro i hi
  apply (NilpotentGrid.mem_coarseIndices_iff hδ hcoords i).mpr
  obtain ⟨x, hxcell, hxD⟩ := hi
  exact ⟨x, hxD, hxcell⟩

theorem finite_retainedIndices {δ : ℝ} (hδ : 0 < δ) {D : Set Plane}
    (hD : Bornology.IsBounded D) (R : ℝ)
    (Q : Index → Plane ≃ₗᵢ[ℝ] Plane) : (retainedIndices δ R D Q).Finite := by
  have hfin : (⋃ i ∈ coarseIndices δ D,
      ({i} ×ˢ {j : Index | infDist (fineCenter δ (Q i) j) (cell δ i) ≤ R})).Finite := by
    apply (finite_coarseIndices hδ hD).biUnion
    intro i hi
    apply (finite_singleton i).prod
    apply finite_fineCenter_neighborhood (Q i) hδ
    · exact (NilpotentGrid.coarseCell_isCompact δ i).isBounded
    · obtain ⟨x, hxcell, _⟩ := hi
      exact ⟨x, hxcell⟩
  apply hfin.subset
  intro ij hij
  exact mem_iUnion.mpr ⟨ij.1, mem_iUnion.mpr ⟨hij.1, by simpa using hij.2⟩⟩

end CylinderCovering.NilpotentRate

end

end OAI
