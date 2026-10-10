import OAI.Analysis.OperatorAlgebra.GNSSeparatingSequence
import OAI.Analysis.OperatorAlgebra.GNSStandardForm
import OAI.Analysis.WeakInfiniteness.CentralState

namespace OAI

/-! The normalized separating vector and its actual positive functional. -/
noncomputable section
open scoped ComplexOrder
namespace WeakPureInfiniteness
open BoundedRecovery KirchbergRordam.GenericRW.GroupedFactors

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma separatingSequence_ne_zero (ξ : H) (hξ : ‖ξ‖ = 1) (d : ℕ → H) :
    separatingSequence ξ d ≠ 0 := by
  intro h
  have he := congrArg (fun x : SequenceHilbert H => x 0) h
  rw [separatingSequence_zero] at he
  have hzero : ξ = 0 := he
  rw [hzero, norm_zero] at hξ
  exact zero_ne_one hξ

def normalizedSeparatingSequence (ξ : H) (d : ℕ → H) : SequenceHilbert H :=
  ((‖separatingSequence ξ d‖⁻¹ : ℝ) : ℂ) • separatingSequence ξ d

lemma normalizedSeparatingSequence_norm (ξ : H) (hξ : ‖ξ‖ = 1) (d : ℕ → H) :
    ‖normalizedSeparatingSequence ξ d‖ = 1 := by
  have hn : ‖separatingSequence ξ d‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (separatingSequence_ne_zero ξ hξ d)
  rw [normalizedSeparatingSequence, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hn]

lemma normalizedSeparatingSequence_separating {A : Type*} [CStarAlgebra A]
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (hξ : ‖ξ‖ = 1)
    (d : ℕ → H) (hd : DenseRange d)
    (T : SequenceHilbert H →L[ℂ] SequenceHilbert H)
    (hT : T ∈ bicommutant (sequenceAmplification π).range)
    (hz : T (normalizedSeparatingSequence ξ d) = 0) : T = 0 := by
  apply sequence_bicommutant_separating π ξ d hd T hT
  rw [normalizedSeparatingSequence, map_smul] at hz
  have hc : (((‖separatingSequence ξ d‖⁻¹ : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast inv_ne_zero (norm_ne_zero_iff.mpr (separatingSequence_ne_zero ξ hξ d))
  exact (smul_eq_zero.mp hz).resolve_left hc

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def vectorPositiveFunctional (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (vectorStateContinuous π.toNonUnitalStarAlgHom ξ).toLinearMap
    (fun _ ha => map_nonneg (vectorStateContinuous_cp π.toNonUnitalStarAlgHom ξ).toMap ha)

lemma vectorPositiveFunctional_apply (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (a : A) :
    vectorPositiveFunctional π ξ a = inner ℂ ξ (π a ξ) := rfl

/-- A dense sequence gives a standard representation with a separating vector. -/
def sequenceStandardGNSData (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ξ : H) (hξ : ‖ξ‖ = 1) (d : ℕ → H) (hd : DenseRange d) :
    CyclicSeparatingData (gnsHilbert (vectorPositiveFunctional (sequenceAmplification π)
      (normalizedSeparatingSequence ξ d))) :=
  standardGNSData _ (sequenceAmplification π) (normalizedSeparatingSequence ξ d)
    (normalizedSeparatingSequence_norm ξ hξ d)
    (vectorPositiveFunctional_apply _ _)
    (normalizedSeparatingSequence_separating π ξ hξ d hd)

end WeakPureInfiniteness

end

end OAI
