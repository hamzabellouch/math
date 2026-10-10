import OAI.Analysis.OperatorAlgebra.IsometricCornerOperators
import OAI.Analysis.CharacterCriterion.FactorIndependence
import OAI.Analysis.ModularRecovery.PositiveKernels
import OAI.Analysis.PureInfiniteness.TwoMatrixNuclear

namespace OAI

/-! A concrete cpc retraction onto a von Neumann algebra restricts to a
concrete cpc retraction onto each represented projection corner. -/

noncomputable section
open scoped InnerProductSpace ComplexOrder

namespace WeakPureInfiniteness
open KirchbergRordam.GenericRW.GroupedFactors

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma isometricCorner_commutant_commutes (M : VonNeumannAlgebra H) (V : K →ₗᵢ[ℂ] H)
    (hp : isometricCornerProjection V ∈ M) (b : M.commutant.toStarSubalgebra) :
    Commute (b : H →L[ℂ] H) (isometricCornerProjection V) :=
  (show Commute (isometricCornerProjection V) (b : H →L[ℂ] H) from
    VonNeumannAlgebra.mem_commutant_iff.mp b.property _ hp).symm

def isometricCornerCommutantHom (M : VonNeumannAlgebra H) (V : K →ₗᵢ[ℂ] H)
    (hp : isometricCornerProjection V ∈ M) :
    M.commutant.toStarSubalgebra →⋆ₐ[ℂ] (K →L[ℂ] K) :=
  isometricCornerRestrictHom V M.commutant.toStarSubalgebra.subtype
    (isometricCorner_commutant_commutes M V hp)

def isometricCornerVonNeumann (M : VonNeumannAlgebra H) (V : K →ₗᵢ[ℂ] H)
    (hp : isometricCornerProjection V ∈ M) : VonNeumannAlgebra K :=
  commutantOf (isometricCornerCommutantHom M V hp).range

lemma isometricCornerVonNeumann_mem_iff (M : VonNeumannAlgebra H) (V : K →ₗᵢ[ℂ] H)
    (hp : isometricCornerProjection V ∈ M) (T : K →L[ℂ] K) :
    T ∈ isometricCornerVonNeumann M V hp ↔ isometricCornerLift V T ∈ M := by
  rw [isometricCornerVonNeumann, mem_commutantOf_iff]
  conv_rhs => rw [← M.commutant_commutant, VonNeumannAlgebra.mem_commutant_iff]
  constructor
  · intro h b hb
    have hc := h _ (show isometricCornerCommutantHom M V hp
      (⟨b, hb⟩ : M.commutant.toStarSubalgebra) ∈
        (isometricCornerCommutantHom M V hp).range from Set.mem_range_self _)
    have ht : Commute T (isometricCornerCompress V b) := hc.symm
    exact ((isometricCornerLift_commute_iff V T b
      (isometricCorner_commutant_commutes M V hp ⟨b, hb⟩)).mpr ht).eq.symm
  · intro h b hb
    obtain ⟨c, rfl⟩ := hb
    have hc : Commute (isometricCornerLift V T) (c : H →L[ℂ] H) :=
      (show Commute (c : H →L[ℂ] H) (isometricCornerLift V T) from h c c.property).symm
    exact ((isometricCornerLift_commute_iff V T c
      (isometricCorner_commutant_commutes M V hp c)).mp hc).symm

lemma isometricCornerCompress_mem (M : VonNeumannAlgebra H) (V : K →ₗᵢ[ℂ] H)
    (hp : isometricCornerProjection V ∈ M) (T : H →L[ℂ] H) (hT : T ∈ M) :
    isometricCornerCompress V T ∈ isometricCornerVonNeumann M V hp := by
  rw [isometricCornerVonNeumann_mem_iff, isometricCornerLift_compress]
  exact M.mul_mem (M.mul_mem hp hT) hp

def isometricCornerExpectation (V : K →ₗᵢ[ℂ] H)
    (E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) :
    (K →L[ℂ] K) →L[ℂ] (K →L[ℂ] K) :=
  (isometricCornerCompress V).comp
    (E.comp (starHomContinuousLinear (isometricCornerLiftHom V)))

lemma isometricCornerExpectation_cp (V : K →ₗᵢ[ℂ] H)
    (E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) (hE : CompletelyPositive E) :
    CompletelyPositive (isometricCornerExpectation V E) :=
  completelyPositive_comp _ _
    (completelyPositive_comp _ _ (starHomContinuous_completelyPositive _) hE)
    (isometricCornerCompress_cp V)

lemma isometricCornerExpectation_norm_le (V : K →ₗᵢ[ℂ] H)
    (E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) (hE : ‖E‖ ≤ 1) :
    ‖isometricCornerExpectation V E‖ ≤ 1 := by
  have hi : ‖E.comp (starHomContinuousLinear (isometricCornerLiftHom V))‖ ≤ 1 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hE (starHomContinuousLinear_norm_le_one _) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul 1))
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (isometricCornerCompress_norm_le V) hi (norm_nonneg _) zero_le_one).trans_eq
      (one_mul 1))

lemma isometricCornerExpectation_mem (M : VonNeumannAlgebra H) (V : K →ₗᵢ[ℂ] H)
    (hp : isometricCornerProjection V ∈ M)
    (E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) (hE : ∀ T, E T ∈ M)
    (T : K →L[ℂ] K) :
    isometricCornerExpectation V E T ∈ isometricCornerVonNeumann M V hp :=
  isometricCornerCompress_mem M V hp _ (hE _)

lemma isometricCornerExpectation_fixed (M : VonNeumannAlgebra H) (V : K →ₗᵢ[ℂ] H)
    (hp : isometricCornerProjection V ∈ M)
    (E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) (hE : ∀ T, T ∈ M → E T = T)
    (T : K →L[ℂ] K) (hT : T ∈ isometricCornerVonNeumann M V hp) :
    isometricCornerExpectation V E T = T := by
  change isometricCornerCompress V (E (isometricCornerLift V T)) = T
  rw [hE _ ((isometricCornerVonNeumann_mem_iff M V hp T).mp hT),
    isometricCornerCompress_lift]

end WeakPureInfiniteness

end

end OAI
