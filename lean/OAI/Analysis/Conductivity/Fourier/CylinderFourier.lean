import Mathlib
import OAI.Analysis.Conductivity.Fourier.TorusPoissonFlow
import OAI.Analysis.Conductivity.Variational.CentralSmoothTrace
import OAI.Analysis.Conductivity.Variational.UniformC1Bounds

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev CylinderL2 (μ : Measure ℝ) :=
  Lp ℂ 2 (μ.prod (volume : Measure (UnitAddTorus (Fin 2))))

lemma cylinderTensor_memLp {μ : Measure ℝ} (f : Lp ℂ 2 μ) (g : TorusL2) :
    MemLp (fun z : ℝ × UnitAddTorus (Fin 2) => f z.1*g z.2) 2
      (μ.prod volume) := by
  apply (memLp_two_iff_integrable_sq_norm
    ((Lp.aestronglyMeasurable f).comp_fst.mul (Lp.aestronglyMeasurable g).comp_snd)).mpr
  simpa only [Pi.mul_apply,norm_mul,mul_pow] using
    ((Lp.memLp f).integrable_norm_pow (by decide : (2:ℕ)≠0)).mul_prod
      ((Lp.memLp g).integrable_norm_pow (by decide : (2:ℕ)≠0))

def cylinderTensor {μ : Measure ℝ} (f : Lp ℂ 2 μ) (g : TorusL2) : CylinderL2 μ :=
  (cylinderTensor_memLp f g).toLp _

lemma cylinderTensor_ae {μ : Measure ℝ} (f : Lp ℂ 2 μ) (g : TorusL2) :
    cylinderTensor f g =ᵐ[μ.prod volume]
      fun z : ℝ × UnitAddTorus (Fin 2) => f z.1*g z.2 :=
  (cylinderTensor_memLp f g).coeFn_toLp

lemma cylinderTensor_add {μ : Measure ℝ} (f f' : Lp ℂ 2 μ) (g : TorusL2) :
    cylinderTensor (f+f') g=cylinderTensor f g+cylinderTensor f' g := by
  apply Lp.ext
  filter_upwards [cylinderTensor_ae (f+f') g,cylinderTensor_ae f g,
    cylinderTensor_ae f' g,Lp.coeFn_add (cylinderTensor f g) (cylinderTensor f' g),
    Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_add f f')] with z hz h1 h2 h3 h4
  rw [hz,h3]
  simp only [Pi.add_apply] at h4 ⊢
  rw [h1,h2,h4]
  exact add_mul _ _ _

lemma cylinderTensor_smul {μ : Measure ℝ} (c : ℂ) (f : Lp ℂ 2 μ) (g : TorusL2) :
    cylinderTensor (c•f) g=c•cylinderTensor f g := by
  apply Lp.ext
  filter_upwards [cylinderTensor_ae (c•f) g,cylinderTensor_ae f g,
    Lp.coeFn_smul c (cylinderTensor f g),
    Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_smul c f)] with z hz h1 h2 h3
  rw [hz,h2]
  simp only [Pi.smul_apply] at h3 ⊢
  rw [h1,h3]
  simp only [smul_eq_mul,mul_assoc]

lemma cylinderTensor_inner {μ : Measure ℝ} [SFinite μ]
    (f f' : Lp ℂ 2 μ) (g g' : TorusL2) :
    inner ℂ (cylinderTensor f g) (cylinderTensor f' g')=
      inner ℂ f f'*inner ℂ g g' := by
  rw [L2.inner_def,L2.inner_def,L2.inner_def,←integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [cylinderTensor_ae f g,cylinderTensor_ae f' g'] with z hz hz'
  rw [hz,hz']
  simp only [RCLike.inner_apply,map_mul]
  ring

lemma cylinderTensor_norm_sq {μ : Measure ℝ} [SFinite μ]
    (f : Lp ℂ 2 μ) (g : TorusL2) :
    ‖cylinderTensor f g‖^2=‖f‖^2*‖g‖^2 := by
  have he := cylinderTensor_inner f f g g
  simp only [inner_self_eq_norm_sq_to_K] at he
  exact_mod_cast he

def cylinderMode (μ : Measure ℝ) [SFinite μ] (h : TorusModes) :
    Lp ℂ 2 μ →ₗᵢ[ℂ] CylinderL2 μ where
  toFun f := cylinderTensor f (mFourierLp 2 h)
  map_add' f g := cylinderTensor_add f g _
  map_smul' c f := cylinderTensor_smul c f _
  norm_map' f := by
    change ‖cylinderTensor f (mFourierLp 2 h)‖=‖f‖
    have he := cylinderTensor_norm_sq f (mFourierLp 2 h)
    rw [(orthonormal_mFourier (d:=Fin 2)).norm_eq_one h,one_pow,mul_one] at he
    nlinarith only [he,norm_nonneg (cylinderTensor f (mFourierLp 2 h)),norm_nonneg f]

lemma cylinderMode_orthogonal (μ : Measure ℝ) [SFinite μ] :
    OrthogonalFamily ℂ (fun _ : TorusModes => Lp ℂ 2 μ) (cylinderMode μ) := by
  intro h k hk f g
  change inner ℂ (cylinderTensor f (mFourierLp 2 h))
    (cylinderTensor g (mFourierLp 2 k))=0
  rw [cylinderTensor_inner,(orthonormal_mFourier (d:=Fin 2)).inner_eq_zero hk,mul_zero]

def cylinderFourier (μ : Measure ℝ) [SFinite μ] :
    lp (fun _ : TorusModes => Lp ℂ 2 μ) 2 →ₗᵢ[ℂ] CylinderL2 μ :=
  (cylinderMode_orthogonal μ).linearIsometry

lemma cylinderFourier_hasSum (μ : Measure ℝ) [SFinite μ]
    (f : lp (fun _ : TorusModes => Lp ℂ 2 μ) 2) :
    HasSum (fun h => cylinderMode μ h (f h)) (cylinderFourier μ f) :=
  (cylinderMode_orthogonal μ).hasSum_linearIsometry f

lemma cylinderFourier_norm_sq (μ : Measure ℝ) [SFinite μ]
    (f : lp (fun _ : TorusModes => Lp ℂ 2 μ) 2) :
    ‖cylinderFourier μ f‖^2=∑' h,‖f h‖^2 := by
  rw [(cylinderFourier μ).norm_map]
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ℝ≥0∞).toReal) f

end ScalarConductivity

end

end OAI
