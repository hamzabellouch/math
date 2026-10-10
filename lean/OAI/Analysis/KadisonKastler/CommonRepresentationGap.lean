import OAI.Analysis.KadisonKastler.GeneratedAlgebraGap
import OAI.Analysis.KadisonKastler.QuotientUnitBall

namespace OAI

/-! # The fiber gap from nearby norm-separable test algebras

The common representation is contractive even when it is not faithful.
Exact contraction lifting to each source algebra then preserves their
ordinary gap. Kaplansky density passes the estimate to the fiber algebras.
-/

namespace KadisonKastler

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem commonRepresentation_unitBall_approx
    (A B C : StarSubalgebra ℂ (H →L[ℂ] H))
    (hAc : IsClosed (A : Set (H →L[ℂ] H)))
    (hBc : IsClosed (B : Set (H →L[ℂ] H)))
    (hCc : IsClosed (C : Set (H →L[ℂ] H)))
    (hAC : A ≤ C) (hBC : B ≤ C) (φ : C →⋆ₐ[ℂ] (K →L[ℂ] K))
    {r : ℝ} (hr : Metric.hausdorffDist (starAlgebraBall A) (starAlgebraBall B) < r)
    {T : K →L[ℂ] K}
    (hT : T ∈ starAlgebraBall (φ.comp (StarSubalgebra.inclusion hAC)).range) :
    ∃ S ∈ starAlgebraBall (φ.comp (StarSubalgebra.inclusion hBC)).range, ‖T - S‖ < r := by
  let := StarSubalgebra.cstarAlgebra A (h_closed := hAc)
  let := StarSubalgebra.cstarAlgebra B (h_closed := hBc)
  let := StarSubalgebra.cstarAlgebra C (h_closed := hCc)
  let φA := φ.comp (StarSubalgebra.inclusion hAC)
  let φB := φ.comp (StarSubalgebra.inclusion hBC)
  obtain ⟨a, han, haT⟩ := exists_contractive_starAlgHom_preimage φA hT.1 hT.2
  obtain ⟨b, hb, hab⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt
    (show (a : H →L[ℂ] H) ∈ starAlgebraBall A from ⟨a.property, han⟩)
    hr (starAlgebraBall_hausdorffEDist_ne_top A B)
  let b' : B := ⟨b, hb.1⟩
  refine ⟨φB b', ⟨⟨b', rfl⟩,
    (NonUnitalStarAlgHom.norm_apply_le φB b').trans hb.2⟩, ?_⟩
  rw [← haT]
  have hnorm : ‖φA a - φB b'‖ ≤ ‖(a : H →L[ℂ] H) - b‖ := by
    change ‖φ (StarSubalgebra.inclusion hAC a) - φ (StarSubalgebra.inclusion hBC b')‖ ≤ _
    rw [← map_sub]
    exact NonUnitalStarAlgHom.norm_apply_le φ _
  exact hnorm.trans_lt (by simpa only [dist_eq_norm] using hab)

theorem kkDistance_commonRepresentation_le (hK : PublishedKaplanskyDensity.{v})
    (A B C : StarSubalgebra ℂ (H →L[ℂ] H))
    (hAc : IsClosed (A : Set (H →L[ℂ] H)))
    (hBc : IsClosed (B : Set (H →L[ℂ] H)))
    (hCc : IsClosed (C : Set (H →L[ℂ] H)))
    (hAC : A ≤ C) (hBC : B ≤ C) (φ : C →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    kkDistance (generatedVonNeumannAlgebra (φ.comp (StarSubalgebra.inclusion hAC)).range)
      (generatedVonNeumannAlgebra (φ.comp (StarSubalgebra.inclusion hBC)).range) ≤
        Metric.hausdorffDist (starAlgebraBall A) (starAlgebraBall B) := by
  apply (kkDistance_generated_le hK _ _).trans
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  apply Metric.hausdorffDist_le_of_mem_dist (Metric.hausdorffDist_nonneg.trans hr.le)
  · intro T hT
    obtain ⟨S, hS, hTS⟩ := commonRepresentation_unitBall_approx A B C hAc hBc hCc hAC hBC φ hr hT
    exact ⟨S, hS, by simpa only [dist_eq_norm] using hTS.le⟩
  · intro S hS
    obtain ⟨T, hT, hST⟩ := commonRepresentation_unitBall_approx B A C hBc hAc hCc hBC hAC φ
      (by simpa only [Metric.hausdorffDist_comm] using hr) hS
    exact ⟨T, hT, by simpa only [dist_eq_norm] using hST.le⟩

end

end KadisonKastler

end OAI
