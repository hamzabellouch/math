import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspFourierTransform

namespace OAI

/-! Single Fourier modes are actual cusp slices. Their finite sums and
completeness prove that the Fourier isometry is onto the radial mode space. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace CubicFirstMoment

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
attribute [local instance] Classical.propDecidable

def cubicThetaTorusBasis (h : Eisenstein) : CubicThetaTorusL2 :=
  UnitAddTorus.mFourierBasis (cubicThetaFourierIndex h)

lemma cubicThetaTorusCoefficient_basis (k h : Eisenstein) :
    cubicThetaTorusCoefficient (cubicThetaTorusBasis h) k=if k=h then 1 else 0 := by
  unfold cubicThetaTorusCoefficient cubicThetaTorusBasis
  rw [← UnitAddTorus.mFourierBasis_repr,HilbertBasis.repr_self]
  simp [lp.single_apply,Pi.single_apply,cubicThetaFourierIndex.injective.eq_iff]

def cubicThetaTorusTensor (h : Eisenstein) : ℂ →L[ℂ] CubicThetaTorusL2 :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight (cubicThetaTorusBasis h)

def cubicThetaTensorSlice (h : Eisenstein) : CubicThetaRadialL2 →L[ℂ] CubicThetaCuspSlices :=
  (cubicThetaTorusTensor h).compLpL 2 volume

lemma cubicThetaTensorSlice_coefficient (h k : Eisenstein) (g : CubicThetaRadialL2) :
    cubicThetaSliceCoefficient k (cubicThetaTensorSlice h g)=if k=h then g else 0 := by
  apply Lp.ext
  filter_upwards [cubicThetaSliceCoefficient_coe k (cubicThetaTensorSlice h g),
    (cubicThetaTorusTensor h).coeFn_compLpL g] with t ht hT
  change cubicThetaTensorSlice h g t=cubicThetaTorusTensor h (g t) at hT
  rw [ht,hT,← cubicThetaTorusCoefficientMap_apply]
  change cubicThetaTorusCoefficientMap k ((g t) • cubicThetaTorusBasis h)=_
  rw [map_smul,cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis]
  by_cases hk : k=h
  · simp [hk]
  · simp [hk]

lemma cubicThetaCuspFourierTransform_tensor (h : Eisenstein) (g : CubicThetaRadialL2) :
    cubicThetaCuspFourierTransform (cubicThetaTensorSlice h g)=
      lp.single 2 h g := by
  apply lp.ext
  funext k
  change cubicThetaSliceCoefficient k (cubicThetaTensorSlice h g)=(lp.single (E:=fun _ : Eisenstein => CubicThetaRadialL2) 2 h g) k
  rw [cubicThetaTensorSlice_coefficient]
  simp only [lp.single_apply,Pi.single_apply]

theorem cubicThetaCuspFourierTransform_surjective :
    Function.Surjective cubicThetaCuspFourierTransform := by
  let R := LinearMap.range cubicThetaCuspFourierTransform.toLinearMap
  have hc : IsClosed (R : Set CubicThetaAllCuspModes) :=
    cubicThetaCuspFourierTransform.isometry.isClosedEmbedding.isClosed_range
  have hs (h : Eisenstein) (g : CubicThetaRadialL2) : lp.single 2 h g∈R :=
    ⟨cubicThetaTensorSlice h g,cubicThetaCuspFourierTransform_tensor h g⟩
  intro F
  have hm : F∈R := hc.mem_of_tendsto (lp.hasSum_single (by simp) F)
    (Filter.Eventually.of_forall (fun s => R.sum_mem (fun h _ => hs h (F h))))
  exact hm

def cubicThetaCuspFourierEquiv : CubicThetaCuspSlices ≃ₗᵢ[ℂ] CubicThetaAllCuspModes :=
  LinearIsometryEquiv.ofSurjective cubicThetaCuspFourierTransform cubicThetaCuspFourierTransform_surjective

end CubicFirstMoment

end

end OAI
