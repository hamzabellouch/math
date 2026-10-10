import OAI.GroupTheory.PolycyclicRecognition.Algebra.CoordinateSchemeSubmersion
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactInverseSections

namespace OAI

/-! # Continuous inverses for the normalized generator schemes

The amplitude differential is square. Its already proved surjectivity is
therefore bijectivity, so compactness supplies a finite set of schemes with
continuous inverse sections on one common coordinate ball.
-/

noncomputable section

namespace PolycyclicRecognition

open Module Set Metric

variable {I V : Type*} [Fintype I] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Measurable endpoint coding for every actual normalized law: the inverse
is continuous on the common ball, and all its amplitudes are bounded by one. -/
theorem exists_uniform_coordinate_inverse_sections {J : Type*} {c : ℕ}
    (a : DynkinCoefficients c 2) (b₀ : Basis J ℝ V) (w₀ : J → FreeMagma I) (C : ℝ) :
    ∃ (schemes : Finset ((Fin (finrank ℝ V) → List (I × ℝ)) ×
        (Fin (finrank ℝ V) → I))) (ε : ℝ), 0 < ε ∧
      ∀ p ∈ normalizedExponentialParameters a w₀ b₀ C,
        ∃ s ∈ schemes, ∃ σ : V → (Fin (finrank ℝ V) → ℝ),
          ContinuousOn σ (ball 0 ε) ∧ ∀ y ∈ ball (0 : V) ε,
            polynomialEndpointScheme a s.1 s.2 p (σ y) = y ∧ ‖σ y‖ < 1 := by
  let f := fun s : (Fin (finrank ℝ V) → List (I × ℝ)) × (Fin (finrank ℝ V) → I) =>
    fun z : ((V →L[ℝ] V →L[ℝ] V) × (I → V)) × (Fin (finrank ℝ V) → ℝ) =>
      polynomialEndpointScheme a s.1 s.2 z.1 z.2
  apply exists_finite_uniform_inverse_sections f
    (isCompact_normalizedExponentialParameters a w₀ b₀ C) _ zero_lt_one
  intro p hp
  rcases hp with ⟨⟨⟨_, _, hB, hw⟩, hg⟩, hc⟩
  obtain ⟨w, i, hz, hs⟩ := exists_coordinate_submersive_scheme a p.1 hB hg hc p.2 b₀ w₀ hw
  refine ⟨(w, i), (contDiff_polynomialEndpointScheme (V := V) (k := 1) a w i).contDiffAt,
    hz, ?_⟩
  let D : (Fin (finrank ℝ V) → ℝ) →L[ℝ] V :=
    (fderiv ℝ (f (w, i)) (p, 0)).comp
      (ContinuousLinearMap.inr ℝ ((V →L[ℝ] V →L[ℝ] V) × (I → V)) _)
  have hsurj : Function.Surjective D := hs
  have hinj : Function.Injective D :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := D.toLinearMap) (by simp)).mpr hsurj
  exact ⟨hinj, hs⟩

end PolycyclicRecognition

end

end OAI
