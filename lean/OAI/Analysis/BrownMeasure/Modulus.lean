import Mathlib
import OAI.Analysis.BrownMeasure.Polar

namespace OAI

noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology ENNReal CStarAlgebra
namespace FiniteFactor
local instance : Module ℝ ProductOp := Module.complexToReal ProductOp
local instance : IsometricContinuousFunctionalCalculus ℝ ProductOp IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus

lemma sourceShift_eq_transport (θ : SourceCoordinate → ℝ) :
    sourceShift SourceCoordinate=sourceTransport θ 0 1 := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [sourceShift_apply_ae u,sourceTransport_apply_ae θ 0 1 u,sourceHilbert_cube] with z hz ht hc
  rw [hz,ht]
  congr 1
  apply Prod.ext
  · funext i
    change z.1 i=Int.fract (z.1 i+(0:ℤ)*θ i)
    simpa using (Int.fract_eq_self.mpr (hc i)).symm
  · rfl

lemma sourceShift_unitary : star (sourceShift SourceCoordinate)*sourceShift SourceCoordinate=1 ∧
    sourceShift SourceCoordinate*star (sourceShift SourceCoordinate)=1 := by
  rw [sourceShift_eq_transport (fun _=>0),sourceTransport_star,sourceTransport_mul,sourceTransport_mul]
  simp [sourceTransport_zero]

def sourceWeightSqrtBase (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) : SourceBaseFunction where
  toFun := fun x=>(Real.sqrt (sourceCocycle θ sourceLogWeight 1 x):ℂ)
  measurable := Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp
    (sourceCocycle_measurable θ sourceLogWeight 1))
  bound := 1
  bound_nonneg := zero_le_one
  norm_le := by
    intro x hx
    rw [Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact (Real.sqrt_le_one).mpr (sourceWeight_le_one θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg hx)

lemma sourceWeight_positive (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    0 ≤ sourcePi θ (sourceWeightBase θ hθ) := by
  let B := sourcePi θ (sourceWeightSqrtBase θ hθ)
  have he : star B*B=sourcePi θ (sourceWeightBase θ hθ) := by
    dsimp [B]
    rw [sourcePi_star]
    apply ContinuousLinearMap.ext
    intro u
    apply Lp.ext
    filter_upwards [sourcePi_apply_ae θ (sourceBaseStar (sourceWeightSqrtBase θ hθ))
      (sourcePi θ (sourceWeightSqrtBase θ hθ) u),sourcePi_apply_ae θ (sourceWeightSqrtBase θ hθ) u,
      sourcePi_apply_ae θ (sourceWeightBase θ hθ) u] with z h1 h2 h3
    change (sourcePi θ (sourceBaseStar (sourceWeightSqrtBase θ hθ))
      (sourcePi θ (sourceWeightSqrtBase θ hθ) u)) z=(sourcePi θ (sourceWeightBase θ hθ) u) z
    rw [h1,h2,h3]
    simp only [sourcePiSymbol,sourceBaseStar,sourceWeightSqrtBase,sourceWeightBase,
      Complex.star_def,Complex.conj_ofReal,← mul_assoc,← Complex.ofReal_mul,
      Real.mul_self_sqrt (sourceCocycle_pos _ _ _ _).le]
  rw [← he]
  exact star_mul_self_nonneg B

lemma sourceOperator_abs (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    CFC.abs (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg)=
      sourcePi θ (sourceWeightBase θ hθ) := by
  let P := sourcePi θ (sourceWeightBase θ hθ)
  have hp : 0 ≤ P := sourceWeight_positive θ hθ
  change CFC.sqrt (star (sourceShift SourceCoordinate*P)*(sourceShift SourceCoordinate*P))=P
  have he : star (sourceShift SourceCoordinate*P)*(sourceShift SourceCoordinate*P)=P*P := by
    rw [star_mul]
    calc
      star P * star (sourceShift SourceCoordinate) * (sourceShift SourceCoordinate * P) =
        star P * ((star (sourceShift SourceCoordinate)*sourceShift SourceCoordinate)*P) := by
          noncomm_ring
      _ = P*P := by rw [sourceShift_unitary.1,one_mul,hp.star_eq]
  rw [he,CFC.sqrt_mul_self P hp]

lemma sourcePolarFamily_zero (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    sourcePolarFamily θ hθ 0=sourcePi θ (sourceWeightBase θ hθ) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [sourcePi_apply_ae θ (sourcePolarBase θ hθ 0) u,
    sourcePi_apply_ae θ (sourceWeightBase θ hθ) u] with z h1 h2
  change (sourcePi θ (sourcePolarBase θ hθ 0) u) z=_
  rw [h1,h2]
  simp [sourcePiSymbol,sourcePolarBase,sourceWeightBase]
  left
  rw [coordinateRotate_add,add_zero]

lemma sourceTransport_conjugate_pi (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (n : ℤ) :
    sourceTransport θ 0 n * sourcePi θ (sourceWeightBase θ hθ)*sourceTransport θ 0 (-n)=
      sourcePolarFamily θ hθ n := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  have ht := (sourceTransportIndex_preserving θ 0 n).quasiMeasurePreserving.ae
    (sourcePi_apply_ae θ (sourceWeightBase θ hθ) (sourceTransport θ 0 (-n) u))
  have hu := (sourceTransportIndex_preserving θ 0 n).quasiMeasurePreserving.ae
    (sourceTransport_apply_ae θ 0 (-n) u)
  filter_upwards [sourceTransport_apply_ae θ 0 n
    (sourcePi θ (sourceWeightBase θ hθ) (sourceTransport θ 0 (-n) u)),ht,hu,
    sourcePi_apply_ae θ (sourcePolarBase θ hθ n) u,sourceHilbert_cube] with z h1 h2 h3 h4 hc
  change (sourceTransport θ 0 n (sourcePi θ (sourceWeightBase θ hθ) (sourceTransport θ 0 (-n) u))) z=_
  change (sourceTransport θ 0 n (sourcePi θ (sourceWeightBase θ hθ) (sourceTransport θ 0 (-n) u))) z=
    (sourcePi θ (sourcePolarBase θ hθ n) u) z
  rw [h1,h2,h3,h4]
  congr 1
  · dsimp [sourcePiSymbol,sourceWeightBase,sourcePolarBase,sourceTransportIndex]
    congr 2
    rw [coordinateRotate_add,coordinateRotate_add]
    congr 1
    ring
  · congr 1
    apply Prod.ext
    · funext i
      simpa [sourceTransportIndex,coordinateRotate] using Int.fract_eq_self.mpr (hc i)
    · simp [sourceTransportIndex]
end FiniteFactor
end

end OAI
