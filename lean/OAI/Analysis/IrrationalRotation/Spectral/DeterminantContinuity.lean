import OAI.Analysis.IrrationalRotation.Spectral.TracialInvertibleDeterminant
import OAI.Analysis.IrrationalRotation.Spectral.QuasinilpotentDeterminantReduction

namespace OAI

noncomputable section
open Filter
open scoped Topology ENNReal CStarAlgebra
namespace Invariant233

variable {A : Type*} [CStarAlgebra A]

theorem continuousOn_log_normSquare :
    ContinuousOn (fun a : A => CFC.log (star a * a)) {a : A | IsUnit a} := by
  apply CFC.continuousOn_log.comp (continuous_star.mul continuous_id).continuousOn
  intro a ha
  exact ⟨by simp [IsSelfAdjoint], ha.star.mul ha⟩

theorem continuousOn_fugledeKadisonDeterminant (τ : TracialState A) :
    ContinuousOn (fugledeKadisonDeterminant τ) {a : A | IsUnit a} := by
  have hc : Continuous (fun b : A =>
      ENNReal.ofReal (Real.exp ((τ b).re / 2))) := by
    apply ENNReal.continuous_ofReal.comp
    fun_prop
  have h := hc.comp_continuousOn (continuousOn_log_normSquare (A := A))
  apply h.congr
  intro a ha
  exact fugledeKadisonDeterminant_of_isUnit τ a ha

theorem continuousAt_fugledeKadisonDeterminant_of_isUnit
    (τ : TracialState A) {a : A} (ha : IsUnit a) :
    ContinuousAt (fugledeKadisonDeterminant τ) a :=
  (continuousOn_fugledeKadisonDeterminant τ a ha).continuousAt
    (Units.isOpen.mem_nhds ha)

theorem continuous_fugledeKadisonDeterminant_one_sub_smul
    (τ : TracialState A) {a : A} (ha : NormQuasinilpotent a) :
    Continuous (fun z : ℂ => fugledeKadisonDeterminant τ (1 - z • a)) := by
  rw [continuous_iff_continuousAt]
  intro z
  exact ContinuousAt.comp (f := fun w : ℂ => (1 : A) - w • a)
    (continuousAt_fugledeKadisonDeterminant_of_isUnit τ (ha.isUnit_one_sub_smul z))
    (by fun_prop)

section Vector
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem continuousOn_vectorFugledeKadisonDeterminant (ξ : H) :
    ContinuousOn (vectorFugledeKadisonDeterminant ξ)
      {T : H →L[ℂ] H | IsUnit T} := by
  have hc : Continuous (fun B : H →L[ℂ] H =>
      ENNReal.ofReal (Real.exp ((vectorTrace ξ B).re / 2))) := by
    apply ENNReal.continuous_ofReal.comp
    unfold vectorTrace
    fun_prop
  have h := hc.comp_continuousOn (continuousOn_log_normSquare (A := H →L[ℂ] H))
  apply h.congr
  intro T hT
  exact vectorFugledeKadisonDeterminant_of_isUnit ξ T hT

theorem continuousAt_vectorFugledeKadisonDeterminant_of_isUnit
    (ξ : H) {T : H →L[ℂ] H} (hT : IsUnit T) :
    ContinuousAt (vectorFugledeKadisonDeterminant ξ) T :=
  (continuousOn_vectorFugledeKadisonDeterminant ξ T hT).continuousAt
    (Units.isOpen.mem_nhds hT)

theorem continuous_vectorFugledeKadisonDeterminant_one_sub_smul
    (ξ : H) {T : H →L[ℂ] H} (hT : NormQuasinilpotent T) :
    Continuous (fun z : ℂ => vectorFugledeKadisonDeterminant ξ (1 - z • T)) := by
  rw [continuous_iff_continuousAt]
  intro z
  exact ContinuousAt.comp (f := fun w : ℂ => (1 : H →L[ℂ] H) - w • T)
    (continuousAt_vectorFugledeKadisonDeterminant_of_isUnit ξ (hT.isUnit_one_sub_smul z))
    (by fun_prop)

end Vector
end Invariant233

end

end OAI
