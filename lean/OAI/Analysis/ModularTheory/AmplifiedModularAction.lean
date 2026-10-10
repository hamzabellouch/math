import OAI.Analysis.ModularTheory.AmplifiedModularExpectation
import OAI.Analysis.OperatorAlgebra.UnitaryMeanRange

namespace OAI

/-! The right modular action normalizes the concrete amplification, and
the modular crossed product is contained in its fixed-point algebra. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure ℝ) [Measure.IsAddRightInvariant μ]
  (S : BoundedRecovery.StandardModularData H)

lemma modular_sigma_mem_commutant (s : ℝ) (b : H →L[ℂ] H) (hb : b ∈ S.M.commutant) :
    S.sigma s b ∈ S.M.commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro a ha
  have h := VonNeumannAlgebra.mem_commutant_iff.mp hb (S.sigma (-s) a) (S.sigma_mem (-s) ha)
  have he := congrArg (S.sigma s) h
  rw [S.sigma_mul, S.sigma_mul] at he
  simpa only [← S.sigma_add_time, add_neg_cancel, S.sigma_zero] using he

lemma modularRightTranslation_pointwise_conjugate (s : ℝ) (b : H →L[ℂ] H) :
    (modularRightTranslationEquiv μ S.D s).conjStarAlgEquiv (pointwiseLpRepresentation μ b) =
      pointwiseLpRepresentation μ (S.sigma s b) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [modularRightTranslation_ae μ S.D s
      (pointwiseLpRepresentation μ b (modularRightTranslation μ S.D (-s) f)),
    (measurePreserving_add_right μ s).quasiMeasurePreserving.ae
      (b.coeFn_compLpL (p := 2) (μ := μ) (modularRightTranslation μ S.D (-s) f)),
    (measurePreserving_add_right μ s).quasiMeasurePreserving.ae
      (modularRightTranslation_ae μ S.D (-s) f),
    (S.sigma s b).coeFn_compLpL (p := 2) (μ := μ) f] with t h₁ h₂ h₃ h₄
  change (modularRightTranslation μ S.D s
    (pointwiseLpRepresentation μ b (modularRightTranslation μ S.D (-s) f))) t =
    ((S.sigma s b).compLpL 2 μ f) t
  change (pointwiseLpRepresentation μ b (modularRightTranslation μ S.D (-s) f)) (t + s) =
    b ((modularRightTranslation μ S.D (-s) f) (t + s)) at h₂
  rw [h₁, h₂, h₃, h₄]
  simp only [add_neg_cancel_right]
  rfl

lemma amplifiedModularAlgebra_invariant (s : ℝ)
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) (hT : T ∈ amplifiedModularAlgebra μ S) :
    orbitConjugate (modularRightTranslationEquiv μ S.D s) T ∈ amplifiedModularAlgebra μ S := by
  apply (mem_amplifiedModularAlgebra μ S _).mpr
  intro b hb
  have hc := (mem_amplifiedModularAlgebra μ S T).mp hT
    (S.sigma s b) (modular_sigma_mem_commutant S s b hb)
  let U := (modularRightTranslationEquiv μ S.D s).conjStarAlgEquiv
  change pointwiseLpRepresentation μ b * U.symm T = U.symm T * pointwiseLpRepresentation μ b
  apply U.injective
  rw [map_mul, map_mul]
  change U (pointwiseLpRepresentation μ b) * U (U.symm T) =
    U (U.symm T) * U (pointwiseLpRepresentation μ b)
  rw [U.apply_symm_apply]
  change U (pointwiseLpRepresentation μ b) * T = T * U (pointwiseLpRepresentation μ b)
  rw [modularRightTranslation_pointwise_conjugate μ S]
  exact hc.eq

lemma modularCore_mem_amplification (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : T ∈ modularCrossedProduct μ S) : T ∈ amplifiedModularAlgebra μ S := by
  apply (mem_amplifiedModularAlgebra μ S T).mpr
  intro b hb
  exact (VonNeumannAlgebra.mem_commutant_iff.mp
    (pointwise_commutant_mem_core_commutant μ S b hb) T hT).symm

lemma modularCore_fixed_right (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : T ∈ modularCrossedProduct μ S) (s : ℝ) (f : Lp H 2 μ) :
    T (modularRightTranslation μ S.D s f) = modularRightTranslation μ S.D s (T f) := by
  have h := VonNeumannAlgebra.mem_commutant_iff.mp
    (modularRightTranslation_mem_commutant μ S s) T hT
  exact congrArg (fun R : Lp H 2 μ →L[ℂ] Lp H 2 μ => R f) h

end WeakPureInfiniteness

end

end OAI
