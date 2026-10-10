import Mathlib
import OAI.Analysis.Conductivity.Variational.AxialDecayL2

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

local instance cylinderFourierCompleteMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance cylinderFourierCompleteProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma cylinderL2_slice_memLp {μ : Measure ℝ} [SFinite μ] (F : CylinderL2 μ) :
    ∀ᵐ t ∂μ, MemLp (fun θ => F (t,θ)) 2 (volume : Measure (UnitAddTorus (Fin 2))) := by
  filter_upwards [(Lp.aestronglyMeasurable F).prodMk_left,
    ((Lp.memLp F).integrable_norm_pow (by decide : (2:ℕ)≠0)).prod_right_ae]
    with t ht hI
  exact (memLp_two_iff_integrable_sq_norm ht).mpr hI

lemma torusFourierCoeff_norm_sq_le {f : UnitAddTorus (Fin 2) → ℂ}
    (hf : MemLp f 2 volume) (h : TorusModes) :
    ‖mFourierCoeff f h‖^2 ≤ ∫ θ, ‖f θ‖^2 := by
  let g : TorusL2 := hf.toLp f
  have he : mFourierCoeff f h = mFourierCoeff g h := by
    unfold mFourierCoeff
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with θ hθ
    rw [hθ]
  rw [he,←mFourierBasis_repr, HilbertBasis.repr_apply_apply]
  have hN := norm_inner_le_norm (𝕜:=ℂ) (mFourierBasis (d:=Fin 2) h) g
  rw [coe_mFourierBasis,(orthonormal_mFourier (d:=Fin 2)).norm_eq_one h,one_mul] at hN
  have heN : ‖g‖^2 = ∫ θ, ‖f θ‖^2 := by
    rw [complexLp_norm_sq]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with θ hθ
    rw [hθ]
  rw [←heN]
  simpa only [coe_mFourierBasis] using pow_le_pow_left₀ (norm_nonneg _) hN 2

def cylinderCoefficient {μ : Measure ℝ} (F : CylinderL2 μ) (h : TorusModes) (t : ℝ) : ℂ :=
  mFourierCoeff (fun θ => F (t,θ)) h

lemma cylinderCoefficient_aestronglyMeasurable {μ : Measure ℝ} [SFinite μ]
    (F : CylinderL2 μ) (h : TorusModes) : AEStronglyMeasurable (cylinderCoefficient F h) μ := by
  exact (((mFourier (-h)).continuous.stronglyMeasurable.aestronglyMeasurable.comp_snd).mul
    (Lp.aestronglyMeasurable F)).integral_prod_right'

lemma cylinderCoefficient_memLp {μ : Measure ℝ} [SFinite μ]
    (F : CylinderL2 μ) (h : TorusModes) : MemLp (cylinderCoefficient F h) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm (cylinderCoefficient_aestronglyMeasurable F h)).mpr
  apply (((Lp.memLp F).integrable_norm_pow (by decide : (2:ℕ)≠0)).integral_prod_left).mono'
    ((cylinderCoefficient_aestronglyMeasurable F h).norm.pow 2)
  filter_upwards [cylinderL2_slice_memLp F] with t ht
  simpa only [Pi.pow_apply,Real.norm_eq_abs,abs_pow,abs_norm,cylinderCoefficient] using
    torusFourierCoeff_norm_sq_le ht h

def cylinderCoefficientLp {μ : Measure ℝ} [SFinite μ]
    (F : CylinderL2 μ) (h : TorusModes) : Lp ℂ 2 μ :=
  (cylinderCoefficient_memLp F h).toLp _

lemma cylinderCoefficientLp_ae {μ : Measure ℝ} [SFinite μ]
    (F : CylinderL2 μ) (h : TorusModes) :
    cylinderCoefficientLp F h =ᵐ[μ] cylinderCoefficient F h :=
  (cylinderCoefficient_memLp F h).coeFn_toLp

lemma cylinderMode_inner_coefficient {μ : Measure ℝ} [SFinite μ]
    (F : CylinderL2 μ) (h : TorusModes) (f : Lp ℂ 2 μ) :
    inner ℂ (cylinderMode μ h f) F = inner ℂ f (cylinderCoefficientLp F h) := by
  have hae : (fun z : ℝ × UnitAddTorus (Fin 2) =>
      inner ℂ ((cylinderMode μ h f) z) (F z)) =ᵐ[μ.prod volume]
      fun z => (starRingEnd ℂ) (f z.1) * (mFourier (-h) z.2 * F z) := by
    filter_upwards [cylinderTensor_ae f (mFourierLp 2 h),
      Measure.quasiMeasurePreserving_snd.ae (coeFn_mFourierLp 2 h)] with z hz he
    change inner ℂ ((cylinderTensor f (mFourierLp 2 h)) z) (F z) = _
    rw [hz,he]
    simp only [RCLike.inner_apply,map_mul,mFourier_neg]
    ring
  have hI := (L2.integrable_inner (cylinderMode μ h f) F).congr hae
  rw [L2.inner_def,L2.inner_def,integral_congr_ae hae,integral_prod _ hI]
  apply integral_congr_ae
  filter_upwards [cylinderCoefficientLp_ae F h] with t ht
  rw [ht,integral_const_mul]
  simp only [cylinderCoefficient,mFourierCoeff,smul_eq_mul,RCLike.inner_apply]
  ring

lemma cylinderModes_total {μ : Measure ℝ} [SFinite μ] (F : CylinderL2 μ)
    (hF : ∀ (h : TorusModes) (f : Lp ℂ 2 μ), inner ℂ (cylinderMode μ h f) F = 0) :
    F = 0 := by
  have hc (h : TorusModes) : cylinderCoefficientLp F h = 0 := by
    apply (inner_self_eq_zero (𝕜:=ℂ)).mp
    exact (cylinderMode_inner_coefficient F h (cylinderCoefficientLp F h)).symm.trans
      (hF h (cylinderCoefficientLp F h))
  have hac (h : TorusModes) : cylinderCoefficient F h =ᵐ[μ] 0 := by
    exact (cylinderCoefficientLp_ae F h).symm.trans (by rw [hc h]; exact Lp.coeFn_zero _ _ _)
  have haslice : ∀ᵐ t ∂μ, ∀ᵐ θ ∂(volume : Measure (UnitAddTorus (Fin 2))), F (t,θ) = 0 := by
    filter_upwards [cylinderL2_slice_memLp F, ae_all_iff.mpr hac] with t ht hct
    let g : TorusL2 := ht.toLp (fun θ => F (t,θ))
    have hcg (h : TorusModes) : mFourierCoeff g h = 0 := by
      calc
        mFourierCoeff g h = cylinderCoefficient F h t := by
          unfold mFourierCoeff cylinderCoefficient
          apply integral_congr_ae
          filter_upwards [ht.coeFn_toLp] with θ hθ
          rw [hθ]
        _ = 0 := hct h
    have hg : g = 0 := by
      apply mFourierBasis.repr.injective
      rw [map_zero]
      ext h
      simpa only [mFourierBasis_repr,lp.coeFn_zero,Pi.zero_apply] using hcg h
    have hg' : g =ᵐ[volume] (0 : UnitAddTorus (Fin 2) → ℂ) := by
      rw [hg]
      exact Lp.coeFn_zero _ _ _
    exact ht.coeFn_toLp.symm.trans hg'
  have hn : ‖F‖^2 = 0 := by
    rw [complexLp_norm_sq,integral_prod _ ((Lp.memLp F).integrable_norm_pow (by decide : (2:ℕ)≠0))]
    apply integral_eq_zero_of_ae
    filter_upwards [haslice] with t ht
    apply integral_eq_zero_of_ae
    filter_upwards [ht] with θ hθ
    simp only [hθ,norm_zero,zero_pow (by decide : (2:ℕ)≠0),Pi.zero_apply]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

theorem cylinderFourier_surjective (μ : Measure ℝ) [SFinite μ] :
    Function.Surjective (cylinderFourier μ) := by
  classical
  let L := (cylinderFourier μ).toContinuousLinearMap
  let K := L.range
  have hclosed : IsClosed (K : Set (CylinderL2 μ)) :=
    (cylinderFourier μ).isometry.isClosedEmbedding.isClosed_range
  let : CompleteSpace K := hclosed.completeSpace_coe
  have horth : Kᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro F hF
    change F = 0
    apply cylinderModes_total F
    intro h f
    apply hF
    exact ⟨lp.single 2 h f,(cylinderMode_orthogonal μ).linearIsometry_apply_single f⟩
  have htop : K = ⊤ := (Submodule.orthogonal_eq_bot_iff).mp horth
  intro F
  have hF : F∈K := by rw [htop]; trivial
  exact hF

def cylinderFourierEquiv (μ : Measure ℝ) [SFinite μ] :
    lp (fun _ : TorusModes => Lp ℂ 2 μ) 2 ≃ₗᵢ[ℂ] CylinderL2 μ :=
  LinearIsometryEquiv.ofSurjective (cylinderFourier μ) (cylinderFourier_surjective μ)

lemma cylinderCoefficient_fourier {μ : Measure ℝ} [SFinite μ]
    (q : lp (fun _ : TorusModes => Lp ℂ 2 μ) 2) (h : TorusModes) :
    cylinderCoefficientLp (cylinderFourier μ q) h = q h := by
  classical
  apply ext_inner_left ℂ
  intro f
  rw [←cylinderMode_inner_coefficient]
  have he : cylinderMode μ h f=cylinderFourier μ (lp.single 2 h f) :=
    ((cylinderMode_orthogonal μ).linearIsometry_apply_single f).symm
  rw [he,(cylinderFourier μ).inner_map_map,lp.inner_single_left]

lemma cylinderFourierEquiv_symm_apply {μ : Measure ℝ} [SFinite μ]
    (F : CylinderL2 μ) (h : TorusModes) :
    (cylinderFourierEquiv μ).symm F h = cylinderCoefficientLp F h := by
  have he := cylinderCoefficient_fourier ((cylinderFourierEquiv μ).symm F) h
  change cylinderCoefficientLp ((cylinderFourierEquiv μ) ((cylinderFourierEquiv μ).symm F)) h=_ at he
  simpa only [LinearIsometryEquiv.apply_symm_apply] using he.symm

theorem cylinderCoefficient_hasSum {μ : Measure ℝ} [SFinite μ] (F : CylinderL2 μ) :
    HasSum (fun h => cylinderMode μ h (cylinderCoefficientLp F h)) F := by
  have hh := cylinderFourier_hasSum μ ((cylinderFourierEquiv μ).symm F)
  simp only [cylinderFourierEquiv_symm_apply] at hh
  change HasSum _ ((cylinderFourierEquiv μ) ((cylinderFourierEquiv μ).symm F)) at hh
  simpa only [LinearIsometryEquiv.apply_symm_apply] using hh

end ScalarConductivity

end
end

end OAI
