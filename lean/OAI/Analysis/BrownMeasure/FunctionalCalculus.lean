import Mathlib
import OAI.Analysis.BrownMeasure.Modulus
import OAI.Analysis.FiniteFactor.Matrix.Covariance
import OAI.Analysis.FiniteFactor.Matrix.Integrals

namespace OAI

noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology
namespace FiniteFactor
local instance : IsometricContinuousFunctionalCalculus ℝ ProductOp IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
abbrev WeightInterval := Set.Icc (0:ℝ) 1

def sourceWeightPoint (θ : SourceCoordinate → ℝ) (x : SourceCoordinate → ℝ) : WeightInterval :=
  ⟨min 1 (sourceCocycle θ sourceLogWeight 1 x),le_min zero_le_one (sourceCocycle_pos _ _ _ _).le,min_le_left _ _⟩
lemma sourceWeightPoint_measurable (θ : SourceCoordinate → ℝ) : Measurable (sourceWeightPoint θ) := by
  apply Measurable.subtype_mk
  exact measurable_const.min (sourceCocycle_measurable θ sourceLogWeight 1)
lemma sourceWeightPoint_val (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    {x : SourceCoordinate → ℝ} (hx : ∀ i,x i∈Set.Ico 0 1) :
    (sourceWeightPoint θ x:ℝ)=sourceCocycle θ sourceLogWeight 1 x :=
  min_eq_right (sourceWeight_le_one θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg hx)

def sourceContinuousWeightBase (θ : SourceCoordinate → ℝ) (φ : C(WeightInterval,ℝ)) : SourceBaseFunction where
  toFun x := (φ (sourceWeightPoint θ x):ℂ)
  measurable := Complex.measurable_ofReal.comp (φ.continuous.measurable.comp (sourceWeightPoint_measurable θ))
  bound := ‖φ‖
  bound_nonneg := norm_nonneg _
  norm_le x _ := by simpa only [Complex.norm_real] using φ.norm_coe_le_norm (sourceWeightPoint θ x)

def sourceContinuousWeight (θ : SourceCoordinate → ℝ) (φ : C(WeightInterval,ℝ)) : ProductOp :=
  sourcePi θ (sourceContinuousWeightBase θ φ)

lemma sourceContinuousWeight_apply_ae (θ : SourceCoordinate → ℝ) (φ : C(WeightInterval,ℝ))
    (u : SourceHilbert SourceCoordinate) :
    sourceContinuousWeight θ φ u=ᵐ[sourceMeasure SourceCoordinate] fun z=>
      (φ (sourceWeightPoint θ (coordinateRotate θ z.2 z.1)):ℂ)*u z :=
  sourcePi_apply_ae θ (sourceContinuousWeightBase θ φ) u

lemma sourceContinuousWeight_one (θ : SourceCoordinate → ℝ) : sourceContinuousWeight θ 1=1 := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [sourceContinuousWeight_apply_ae θ 1 u] with z hz
  change (sourceContinuousWeight θ 1 u) z=u z
  simpa using hz
lemma sourceContinuousWeight_zero (θ : SourceCoordinate → ℝ) : sourceContinuousWeight θ 0=0 := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [sourceContinuousWeight_apply_ae θ 0 u,Lp.coeFn_zero ℂ 2 (sourceMeasure SourceCoordinate)] with z hz h0
  change (sourceContinuousWeight θ 0 u) z=(0:SourceHilbert SourceCoordinate) z
  rw [h0]
  simpa using hz
lemma sourceContinuousWeight_add (θ : SourceCoordinate → ℝ) (φ ψ : C(WeightInterval,ℝ)) :
    sourceContinuousWeight θ (φ+ψ)=sourceContinuousWeight θ φ+sourceContinuousWeight θ ψ := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [sourceContinuousWeight_apply_ae θ (φ+ψ) u,sourceContinuousWeight_apply_ae θ φ u,
    sourceContinuousWeight_apply_ae θ ψ u,Lp.coeFn_add (sourceContinuousWeight θ φ u) (sourceContinuousWeight θ ψ u)] with z ha hf hg hs
  change (sourceContinuousWeight θ (φ+ψ) u) z=(sourceContinuousWeight θ φ u+sourceContinuousWeight θ ψ u) z
  rw [ha,hs,Pi.add_apply,hf,hg]
  simp [add_mul]
lemma sourceContinuousWeight_mul (θ : SourceCoordinate → ℝ) (φ ψ : C(WeightInterval,ℝ)) :
    sourceContinuousWeight θ (φ*ψ)=sourceContinuousWeight θ φ*sourceContinuousWeight θ ψ := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [sourceContinuousWeight_apply_ae θ (φ*ψ) u,
    sourceContinuousWeight_apply_ae θ φ (sourceContinuousWeight θ ψ u),sourceContinuousWeight_apply_ae θ ψ u] with z ha hf hg
  change (sourceContinuousWeight θ (φ*ψ) u) z=(sourceContinuousWeight θ φ (sourceContinuousWeight θ ψ u)) z
  rw [ha,hf,hg]
  simp [mul_assoc]
lemma sourceContinuousWeight_smul (θ : SourceCoordinate → ℝ) (r : ℝ) (φ : C(WeightInterval,ℝ)) :
    sourceContinuousWeight θ (r • φ)=r • sourceContinuousWeight θ φ := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [sourceContinuousWeight_apply_ae θ (r • φ) u,sourceContinuousWeight_apply_ae θ φ u,
    Lp.coeFn_smul r (sourceContinuousWeight θ φ u)] with z ha hf hs
  change (sourceContinuousWeight θ (r • φ) u) z=(r • sourceContinuousWeight θ φ u) z
  rw [ha,hs,Pi.smul_apply,hf]
  simp [Complex.real_smul,mul_assoc]
lemma sourceContinuousWeight_star (θ : SourceCoordinate → ℝ) (φ : C(WeightInterval,ℝ)) :
    sourceContinuousWeight θ (star φ)=star (sourceContinuousWeight θ φ) := by
  change sourcePi θ (sourceContinuousWeightBase θ (star φ))=star (sourcePi θ (sourceContinuousWeightBase θ φ))
  rw [sourcePi_star]
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [sourcePi_apply_ae θ (sourceContinuousWeightBase θ (star φ)) u,
    sourcePi_apply_ae θ (sourceBaseStar (sourceContinuousWeightBase θ φ)) u] with z h1 h2
  rw [h1,h2]
  simp [sourcePiSymbol,sourceContinuousWeightBase,sourceBaseStar]

def sourceContinuousWeightHom (θ : SourceCoordinate → ℝ) : C(WeightInterval,ℝ) →⋆ₐ[ℝ] ProductOp where
  toFun := sourceContinuousWeight θ
  map_one' := sourceContinuousWeight_one θ
  map_zero' := sourceContinuousWeight_zero θ
  map_add' := sourceContinuousWeight_add θ
  map_mul' := sourceContinuousWeight_mul θ
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one,sourceContinuousWeight_smul,sourceContinuousWeight_one,Algebra.algebraMap_eq_smul_one]
  map_star' := sourceContinuousWeight_star θ

lemma sourceContinuousWeightHom_continuous (θ : SourceCoordinate → ℝ) : Continuous (sourceContinuousWeightHom θ) := by
  exact ((sourceContinuousWeightHom θ).toAlgHom.toLinearMap.mkContinuous (1:ℝ)
    (fun φ=>by
      change ‖sourcePi θ (sourceContinuousWeightBase θ φ)‖ ≤ 1*‖φ‖
      simpa only [one_mul, sourceContinuousWeightBase] using sourcePi_norm_le θ (sourceContinuousWeightBase θ φ))).continuous

lemma sourceContinuousWeight_id (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    sourceContinuousWeight θ ((ContinuousMap.id ℝ).restrict WeightInterval)=sourcePi θ (sourceWeightBase θ hθ) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [sourceContinuousWeight_apply_ae θ ((ContinuousMap.id ℝ).restrict WeightInterval) u,
    sourcePi_apply_ae θ (sourceWeightBase θ hθ) u] with z h1 h2
  change (sourceContinuousWeight θ _ u) z=(sourcePi θ (sourceWeightBase θ hθ) u) z
  rw [h1,h2]
  simp only [ContinuousMap.restrict_apply,ContinuousMap.id_apply,
    sourcePiSymbol,sourceWeightBase]
  have hc : ∀ i,coordinateRotate θ z.2 z.1 i∈Set.Ico (0:ℝ) 1 := by
    intro i
    exact ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
  rw [sourceWeightPoint_val θ hθ hc]

lemma sourceWeight_spectrum_subset (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    spectrum ℝ (sourcePi θ (sourceWeightBase θ hθ))⊆WeightInterval := by
  intro t ht
  exact ⟨spectrum_nonneg_of_nonneg (sourceWeight_positive θ hθ) ht,
    (Real.le_norm_self t).trans ((spectrum.norm_le_norm_of_mem ht).trans (sourcePi_norm_le θ (sourceWeightBase θ hθ)))⟩

lemma sourceContinuousWeightHom_eq_cfc (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    sourceContinuousWeightHom θ=cfcHomSuperset (sourceWeight_positive θ hθ).isSelfAdjoint (sourceWeight_spectrum_subset θ hθ) := by
  apply ContinuousMap.UniqueHom.eq_of_continuous_of_map_id
  · exact sourceContinuousWeightHom_continuous θ
  · exact cfcHomSuperset_continuous _ _
  · rw [cfcHomSuperset_id]
    exact sourceContinuousWeight_id θ hθ

lemma sourcePi_trace (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) :
    sourceVacuumFunctional (sourcePi θ g)=∫ x,g.toFun x ∂sourceBaseMeasure := by
  rw [sourceVacuumFunctional_matrixIntegral]
  apply integral_congr_ae
  filter_upwards [sourceMatrixEntry_pi θ g 0,sourceSamplingHaar_cube] with x hx hc
  have hr : coordinateRotate θ 0 x=x := by
    funext i
    simpa [coordinateRotate] using Int.fract_eq_self.mpr (hc i)
  simpa only [hr,ite_true] using hx 0
end FiniteFactor
end

end OAI
