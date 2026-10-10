import Mathlib
import OAI.Analysis.Conductivity.Flux.AttachedPhysicalSmoothGreen
import OAI.Analysis.Conductivity.Variational.PhysicalTraceBounds

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def smoothOuterContinuousL (i : Fin 3) :
    SmoothScalar (Fin 3 → ℝ) →ₗ[ℝ] C(UnitAddTorus (Fin 2),ℂ) where
  toFun φ := ⟨fun θ => (φ.val (physicalOuterBoundary i θ):ℂ),
    Complex.continuous_ofReal.comp ((smoothScalar_contDiff φ).continuous.comp (physicalOuterBoundary_continuous i))⟩
  map_add' f g := by ext θ; simp
  map_smul' c f := by ext θ; simp

def smoothOuterFourierL (i : Fin 3) :
    SmoothScalar (Fin 3 → ℝ) →ₗ[ℝ] SpectralL2 TorusModes :=
  ((mFourierBasis (d:=Fin 2)).repr.toLinearEquiv.toLinearMap.restrictScalars ℝ).comp
    ((ContinuousMap.toLp 2 volume ℝ).toLinearMap.comp (smoothOuterContinuousL i))

lemma smoothOuterFourierL_apply (i : Fin 3) (φ : SmoothScalar (Fin 3 → ℝ)) (h : TorusModes) :
    smoothOuterFourierL i φ h=mFourierCoeff (fun θ => (φ.val (physicalOuterBoundary i θ):ℂ)) h := by
  change (mFourierBasis (d:=Fin 2)).repr (ContinuousMap.toLp 2 volume ℂ (smoothOuterContinuousL i φ)) h=_
  rw [mFourierBasis_repr,mFourierCoeff_toLp]
  rfl

lemma smoothOuterFourierL_sq (i : Fin 3) (φ : SmoothScalar (Fin 3 → ℝ)) :
    ‖smoothOuterFourierL i φ‖^2=∫ θ : UnitAddTorus (Fin 2),(φ.val (physicalOuterBoundary i θ))^2 := by
  change ‖(mFourierBasis (d:=Fin 2)).repr (ContinuousMap.toLp 2 volume ℂ (smoothOuterContinuousL i φ))‖^2=_
  rw [LinearIsometryEquiv.norm_map,←real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (smoothOuterContinuousL i φ) (p:=2) (μ:=volume) (𝕜:=ℂ)] with θ hθ
  rw [hθ,real_inner_self_eq_norm_sq]
  simp [smoothOuterContinuousL,Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma smoothOuterFourierL_bound (i : Fin 3) :
    ∃ C : ℝ,∀ φ,‖smoothOuterFourierL i φ‖≤C*‖smoothPiH1L φ‖ := by
  obtain ⟨C,hC,hb⟩ := physicalOuter_smooth_sq_bound i
  refine ⟨Real.sqrt C,fun φ => ?_⟩
  have hh := hb φ.val (smoothScalar_contDiff φ)
  simp only [volume_pi,unitCircle_volume_eq_haar] at hh
  have hh' : ‖smoothOuterFourierL i φ‖^2≤C*‖smoothPiH1L φ‖^2 := by
    rw [smoothOuterFourierL_sq]
    exact hh
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg _))).mp
  simpa only [mul_pow,Real.sq_sqrt hC] using hh'

def physicalOuterTraceCLM (i : Fin 3) : H1 →L[ℝ] SpectralL2 TorusModes :=
  (dense_linear_observable_extension smoothPiH1L (smoothOuterFourierL i)
    smoothPiH1L_dense (smoothOuterFourierL_bound i)).choose

lemma physicalOuterTrace_smooth (i : Fin 3) {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (s : Fin 3 → ℝ) :
    physicalOuterTraceCLM i (piSmoothH1 hφ)=(physicalSmoothOuterTrace s hφ i).val 0 := by
  have he := (dense_linear_observable_extension smoothPiH1L (smoothOuterFourierL i)
    smoothPiH1L_dense (smoothOuterFourierL_bound i)).choose_spec ⟨φ,hφ⟩
  change physicalOuterTraceCLM i (piSmoothH1 hφ)=smoothOuterFourierL i ⟨φ,hφ⟩ at he
  rw [he]
  ext h
  rw [smoothOuterFourierL_apply]
  refine Fin.cases ?_ (fun k => ?_) i
  · exact (smoothCollarTrace_fst s 0 hφ h).symm
  · exact (smoothCollarTrace_fst s 0 (hφ.comp (sourceChildCoordinates_contDiff (actualChildSign k))) h).symm

end ScalarConductivity

end
end

end OAI
