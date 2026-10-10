import OAI.Analysis.KadisonKastler.RegularWeightedIntegral
import OAI.Analysis.KadisonKastler.RegularCommutantPackets
import OAI.Analysis.KadisonKastler.RegularCoreDensePeriods

namespace OAI

/-! # Integrable convolution operators in the regular commutant

The common regular action is strongly continuous by its gauge
equivalence to translations. Its integrable scalar averages belong to
the generated commutant algebra. Products of two such averages with a
constant commutant coefficient give the finite packet averages used in
the reconstruction argument.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))

include hU in
/-- The common regular action inherits strong continuity from translations. -/
theorem continuous_regularCoreAction (f : RegularCoreHilbert H) :
    Continuous (fun t : ℝ => (regularCoreAction U (Multiplicative.ofAdd t) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) := by
  have he (t : ℝ) :
      (regularCoreAction U (Multiplicative.ofAdd t) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f =
      (star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        (regularTranslateApply t
          ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)) := by
    rw [regularCoreAction_eq_gauged_translation U hU]
    rw [Unitary.conjStarAlgAut_star_apply]
    rfl
  simp_rw [he]
  exact (star (regularGauge U hU) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H).continuous.comp
      (continuous_regularTranslateApply _)

private theorem regularCoreAction_norm_le_one (t : ℝ) :
    ‖(regularCoreAction U (Multiplicative.ofAdd t) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simp only [Unitary.norm_map, one_mul, le_refl]

/-- The convolution convention uses the action at `-t`. -/
def regularActionIntegral (w : ℝ → ℂ) (hw : Integrable w volume) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
  weightedOperatorIntegral volume w hw
    (fun t => (regularCoreAction U (Multiplicative.ofAdd (-t)) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (fun f => ((continuous_regularCoreAction U hU f).comp continuous_neg).aestronglyMeasurable)
    1 (Filter.Eventually.of_forall fun t => regularCoreAction_norm_le_one U (-t))

theorem norm_regularActionIntegral_le (w : ℝ → ℂ) (hw : Integrable w volume) :
    ‖regularActionIntegral U hU w hw‖ ≤ ∫ t : ℝ, ‖w t‖ := by
  simpa only [regularActionIntegral, mul_one] using norm_weightedOperatorIntegral_le volume w hw
    (fun t => (regularCoreAction U (Multiplicative.ofAdd (-t)) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (fun f => ((continuous_regularCoreAction U hU f).comp continuous_neg).aestronglyMeasurable)
    1 zero_le_one (Filter.Eventually.of_forall fun t => regularCoreAction_norm_le_one U (-t))

/-- No normalizer hypothesis is needed for these explicit generators. -/
theorem regularActionIntegral_mem (P : VonNeumannAlgebra H)
    (w : ℝ → ℂ) (hw : Integrable w volume) :
    regularActionIntegral U hU w hw ∈ regularCommutantAlgebra U P := by
  apply weightedOperatorIntegral_mem
  apply Filter.Eventually.of_forall
  intro t
  exact subset_generatedVonNeumannAlgebra _
    (StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨Multiplicative.ofAdd (-t), rfl⟩))

/-- The finite packet average has a factored, algebra-valued realization. -/
def regularPacketConvolution
    (φ ψ : ℝ → ℂ) (hφ : Integrable φ volume) (hψ : Integrable ψ volume)
    (A : H →L[ℂ] H) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
  regularActionIntegral U hU φ hφ * regularConstantHom (volume : Measure ℝ) A *
    star (regularActionIntegral U hU ψ hψ)

theorem regularPacketConvolution_mem (P : VonNeumannAlgebra H)
    (φ ψ : ℝ → ℂ) (hφ : Integrable φ volume) (hψ : Integrable ψ volume)
    {A : H →L[ℂ] H} (hA : A ∈ P.commutant) :
    regularPacketConvolution U hU φ ψ hφ hψ A ∈ regularCommutantAlgebra U P := by
  apply (regularCommutantAlgebra U P).mul_mem
  · apply (regularCommutantAlgebra U P).mul_mem
    · exact regularActionIntegral_mem U hU P φ hφ
    · exact subset_generatedVonNeumannAlgebra _
        (StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨A, hA, rfl⟩))
  · exact (regularCommutantAlgebra U P).star_mem'
      (regularActionIntegral_mem U hU P ψ hψ)

end

end KadisonKastler

end OAI
