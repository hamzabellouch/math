import OAI.Analysis.KadisonKastler.RegularPacketAveraging
import OAI.Analysis.KadisonKastler.RegularPacketCompression

namespace OAI

/-! # Localization of finite packet matrices

Cutting off a packet cuts off its scalar coefficient. The localized
average of each packet matrix is consequently a product of the actual
convolution generators, not an assumed measurable operator integral.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private def regularSandwichLinear
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (V : E →L[ℂ] F) : (F →L[ℂ] F) →ₗ[ℂ] (E →L[ℂ] E) where
  toFun T := V.adjoint.comp (T.comp V)
  map_add' T S := by
    apply ContinuousLinearMap.ext
    intro x
    change V.adjoint (T (V x) + S (V x)) = V.adjoint (T (V x)) + V.adjoint (S (V x))
    exact map_add V.adjoint _ _
  map_smul' c T := by
    apply ContinuousLinearMap.ext
    intro x
    change V.adjoint (c • T (V x)) = c • V.adjoint (T (V x))
    exact map_smul V.adjoint c _

/-- Linearity in the operator being localized and averaged. -/
def regularLocalizationAverageLinear
    (s : Set ℝ) (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤) :
    (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) →ₗ[ℂ]
      (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
  (regularSandwichLinear (regularLocalFrame (H := H) s hs hfinite)).comp
    (regularConstantHom (H := RegularCoreHilbert H) (volume : Measure ℝ)).toAlgHom.toLinearMap

theorem integrable_regularIndicatorPacket
    (s : Set ℝ) (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤)
    (φ : Lp ℂ 2 (volume : Measure ℝ)) :
    Integrable (regularIndicatorProjection (H := ℂ) s hs φ) volume := by
  let : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr hfinite
  have h := ((Lp.memLp φ).restrict s).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  exact ((integrable_indicator_iff hs).mpr h).congr
    (regularIndicatorProjection_apply_ae s hs φ).symm

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))

theorem regularIndicatorProjection_gaugedPacket
    (s : Set ℝ) (hs : MeasurableSet s)
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (x : H) :
    regularIndicatorProjection s hs (regularGaugedPacket U hU φ x) =
      regularGaugedPacket U hU (regularIndicatorProjection s hs φ) x := by
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae s hs (regularGaugedPacket U hU φ x),
    regularGaugedPacket_apply_ae U hU φ x,
    regularGaugedPacket_apply_ae U hU (regularIndicatorProjection s hs φ) x,
    regularIndicatorProjection_apply_ae s hs φ] with t hcut hφ hpacket hscalar
  rw [hcut, hpacket, hscalar]
  by_cases ht : t ∈ s
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, hφ]
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_smul, map_zero]

theorem regularGaugedPacket_adjoint_indicator
    (s : Set ℝ) (hs : MeasurableSet s)
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (f : RegularCoreHilbert H) :
    (regularGaugedPacket U hU φ).adjoint (regularIndicatorProjection s hs f) =
      (regularGaugedPacket U hU (regularIndicatorProjection s hs φ)).adjoint f := by
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right,
    ← regularIndicatorProjection_gaugedPacket]
  have hQ := (regularIndicatorProjection_isStarProjection (H := H) s hs).isSelfAdjoint
  have he : (regularIndicatorProjection (H := H) s hs).adjoint =
      regularIndicatorProjection s hs := by
    rw [← ContinuousLinearMap.star_eq_adjoint, hQ.star_eq]
  simpa only [he] using (ContinuousLinearMap.adjoint_inner_right
    (regularIndicatorProjection (H := H) s hs) (regularGaugedPacket U hU φ x) f)

/-- A rank-one scalar packet matrix with an arbitrary bounded vector coefficient. -/
def regularPacketOperator
    (φ ψ : Lp ℂ 2 (volume : Measure ℝ)) (A : H →L[ℂ] H) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
  (regularGaugedPacket U hU φ).comp (A.comp (regularGaugedPacket U hU ψ).adjoint)

theorem regularLocalizationAverage_packetOperator
    (s : Set ℝ) (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤)
    (φ ψ : Lp ℂ 2 (volume : Measure ℝ)) (A : H →L[ℂ] H) :
    regularLocalizationAverage s hs hfinite (regularPacketOperator U hU φ ψ A) =
      regularPacketConvolution U hU
        (regularIndicatorProjection s hs φ) (regularIndicatorProjection s hs ψ)
        (integrable_regularIndicatorPacket s hs hfinite φ)
        (integrable_regularIndicatorPacket s hs hfinite ψ) A := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro f
  rw [inner_regularLocalizationAverage,
    ← integral_packet_orbit_inner_eq]
  apply integral_congr_ae
  filter_upwards [] with r
  change inner ℂ (regularIndicatorProjection s hs (regularTranslateApply r f))
    (regularGaugedPacket U hU φ (A ((regularGaugedPacket U hU ψ).adjoint
      (regularIndicatorProjection s hs (regularTranslateApply r g))))) = _
  rw [← ContinuousLinearMap.adjoint_inner_left,
    regularGaugedPacket_adjoint_indicator, regularGaugedPacket_adjoint_indicator]

theorem regularLocalizationAverage_packetOperator_mem
    (P : VonNeumannAlgebra H)
    (s : Set ℝ) (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤)
    (φ ψ : Lp ℂ 2 (volume : Measure ℝ)) (A : H →L[ℂ] H) (hA : A ∈ P.commutant) :
    regularLocalizationAverage s hs hfinite (regularPacketOperator U hU φ ψ A) ∈
      regularCommutantAlgebra U P := by
  rw [regularLocalizationAverage_packetOperator]
  exact regularPacketConvolution_mem U hU P _ _ _ _ hA

/-- Every finite compression has its localized average in the candidate commutant. -/
theorem regularLocalizationAverage_compression_mem
    (P : VonNeumannAlgebra H)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ A ∈ P, Commute T (regularCoreEmbedding U hU A))
    (s : Set ℝ) (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤)
    (d : Finset ℕ) :
    regularLocalizationAverage s hs hfinite
      (regularPacketProjection U hU d * T * regularPacketProjection U hU d) ∈
      regularCommutantAlgebra U P := by
  have he : regularPacketProjection U hU d * T * regularPacketProjection U hU d =
      ∑ i ∈ d, ∑ j ∈ d, regularPacketOperator U hU (regularScalarBasis i)
        (regularScalarBasis j)
        (regularPacketCoefficient U hU T (regularScalarBasis i) (regularScalarBasis j)) := by
    apply ContinuousLinearMap.ext
    intro f
    simpa only [sum_apply, regularPacketOperator, ContinuousLinearMap.comp_apply] using
      regularPacketCompression_apply U hU T d f
  rw [he]
  change regularLocalizationAverageLinear s hs hfinite _ ∈ _
  rw [map_sum]
  apply (regularCommutantAlgebra U P).sum_mem
  intro i hi
  rw [map_sum]
  apply (regularCommutantAlgebra U P).sum_mem
  intro j hj
  exact regularLocalizationAverage_packetOperator_mem U hU P s hs hfinite _ _ _
    (regularPacketCoefficient_mem_commutant U hU P T hT _ _)

/-- Bounded weak convergence removes the finite packet compression. -/
theorem regularLocalizationAverage_mem
    (P : VonNeumannAlgebra H)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ A ∈ P, Commute T (regularCoreEmbedding U hU A))
    (s : Set ℝ) (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤) :
    regularLocalizationAverage s hs hfinite T ∈ regularCommutantAlgebra U P := by
  let a (d : Finset ℕ) : Algebra (regularCommutantAlgebra U P) :=
    ⟨regularLocalizationAverage s hs hfinite
      (regularPacketProjection U hU d * T * regularPacketProjection U hU d),
      regularLocalizationAverage_compression_mem U hU P T hT s hs hfinite d⟩
  apply Generator.Tracial.weak_operator_limit_mem (l := atTop) _ a
  intro f g
  exact regularLocalizationAverage_tendsto_weak s hs hfinite _ T ‖T‖
    (Eventually.of_forall (regularPacketCompression_norm_le U hU T))
    (regularPacketCompression_tendsto_weak U hU T) f g

end

end KadisonKastler

end OAI
