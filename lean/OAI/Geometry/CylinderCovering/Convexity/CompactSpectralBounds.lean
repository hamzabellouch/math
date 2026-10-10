import OAI.Geometry.RuledCovering.Main

namespace OAI

noncomputable section
open Set
namespace RuledApproximation

theorem compact_spectral_envelope {X : Type*} [TopologicalSpace X]
    {D : Set X} (hD : IsCompact D) {A : X → Plane →L[ℝ] Plane}
    (hA : ContinuousOn A D)
    (htr : ∀ p ∈ D, LinearMap.trace ℝ Plane (A p).toLinearMap = 0)
    (hdet : ∀ p ∈ D, LinearMap.det (A p).toLinearMap < 0) :
    ∃ m B : ℝ, 0 < m ∧ 0 < B ∧ ∀ p ∈ D,
      m ≤ Real.sqrt (-LinearMap.det (A p).toLinearMap) ∧
      Real.sqrt (-LinearMap.det (A p).toLinearMap) ≤ B ∧ ‖A p‖ ≤ B := by
  by_cases hne : D.Nonempty
  · have hlam : ContinuousOn (fun p => Real.sqrt (-LinearMap.det (A p).toLinearMap)) D :=
      Real.continuous_sqrt.comp_continuousOn
        (ContinuousLinearMap.continuous_det.comp_continuousOn hA).neg
    obtain ⟨p, hp, hmin⟩ := hD.exists_isMinOn hne hlam
    obtain ⟨B, hB⟩ := hD.exists_bound_of_continuousOn hA
    refine ⟨Real.sqrt (-LinearMap.det (A p).toLinearMap), max 1 B,
      Real.sqrt_pos.mpr (neg_pos.mpr (hdet p hp)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro q hq
    refine ⟨hmin hq, ?_, (hB q hq).trans (le_max_right _ _)⟩
    exact (eigenvalue_le_norm (A q) (Real.sqrt_nonneg _)
      (plane_hyperbolic_eigenvalues (A q).toLinearMap (htr q hq) (hdet q hq)).1).trans
      ((hB q hq).trans (le_max_right _ _))
  · refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro p hp
    exact (hne ⟨p, hp⟩).elim

end RuledApproximation

end

end OAI
