import OAI.Analysis.KadisonSimilarity.Representation.ConcretePredualDuality

namespace OAI

/-! A separable concrete Hilbert space gives a separable Banach predual.
Only the norm-continuity of vector coefficients and their defining density
are used. -/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H)

def predualCoefficientBilinear : H →L[ℂ] H →L⋆[ℂ] ConcretePredual M :=
  (LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (predualCoefficient M)
    (predualCoefficient_add_left M) (predualCoefficient_smul_left M)
    (predualCoefficient_add_right M) (predualCoefficient_smul_right M)).mkContinuous₂ 1
      (fun x y => by
        change ‖predualCoefficient M x y‖ ≤ 1 * ‖x‖ * ‖y‖
        simpa only [one_mul] using predualCoefficient_norm_le M x y)

theorem predualCoefficient_continuous :
    Continuous (fun p : H × H => predualCoefficient M p.1 p.2) := by
  change Continuous (fun p : H × H => predualCoefficientBilinear M p.1 p.2)
  exact ((predualCoefficientBilinear M).flip.continuous.comp continuous_snd).clm_apply
    continuous_fst

theorem normalCoefficient_continuous :
    Continuous (fun p : H × H => normalCoefficient M p.1 p.2) := by
  exact (normalFunctionalSpace M).toSubmodule.subtypeL.continuous.comp
    (predualCoefficient_continuous M)

/-- The vector predual has a countable norm-dense subset whenever the
represented Hilbert space does. -/
instance concretePredual_separable [TopologicalSpace.SeparableSpace H] :
    TopologicalSpace.SeparableSpace (ConcretePredual M) := by
  have hs := TopologicalSpace.isSeparable_range (normalCoefficient_continuous M)
  have hc : TopologicalSpace.IsSeparable (normalFunctionalSpace M : Set
      (StrongDual ℂ M.toStarSubalgebra)) := hs.span.closure
  exact hc.separableSpace

end KadisonSimilarity

end

end OAI
