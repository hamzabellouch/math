import OAI.Geometry.EinsteinFour.MetricDoubleCover
import OAI.Geometry.EinsteinFour.CP2InvolutionFixed

namespace OAI

/-! The two-model cover reduction without Euler-characteristic assumptions.
A free deck involution cannot act isometrically on the Fubini--Study model. -/

namespace PositiveEinsteinFour

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

universe u v

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace FourSpace M] [ChartedSpace FourSpace N]
  [IsManifold I4 ∞ M] [IsManifold I4 ∞ N]
  {g : SmoothMetric M} {h : SmoothMetric N}

theorem MetricDoubleCover.not_projective (C : MetricDoubleCover g h)
    (a : ℝ) (ha : 0 < a) : ¬ ScaledIsometricTo h a fubiniStudyDistance := by
  rintro ⟨e, he⟩
  let f : ComplexProjective2 → ComplexProjective2 := fun p => e (C.deck (e.symm p))
  have hinv : Function.Involutive f := by
    intro p
    simp only [f, e.symm_apply_apply, C.involutive (e.symm p), e.apply_symm_apply]
  have hdist (p q : ComplexProjective2) :
      fubiniStudyDistance (f p) (f q) = fubiniStudyDistance p q := by
    apply (ENNReal.ofReal_eq_ofReal_iff
      (Real.arccos_nonneg _) (Real.arccos_nonneg _)).mp
    change ENNReal.ofReal (fubiniStudyDistance (e (C.deck (e.symm p)))
      (e (C.deck (e.symm q)))) = _
    rw [he, C.deck_distance_scaled a ha.le, ← he]
    simp only [e.apply_symm_apply]
    rfl
  obtain ⟨p, hp⟩ := cp2_involutive_isometry_fixed f hinv hdist
  have hfixed : C.deck (e.symm p) = e.symm p := by
    apply e.injective
    simpa only [f, e.apply_symm_apply] using hp
  exact C.free (e.symm p) hfixed

theorem MetricDoubleCover.classified_of_two_models_direct (C : MetricDoubleCover g h)
    (hmodels : ∃ a : ℝ, 0 < a ∧
      (ScaledIsometricTo h a roundDistance ∨ ScaledIsometricTo h a fubiniStudyDistance)) :
    Classified g := by
  obtain ⟨a, ha, hs | hp⟩ := hmodels
  · exact C.classified_of_round a ha hs
  · exact (C.not_projective a ha hp).elim

end
end PositiveEinsteinFour

end OAI
