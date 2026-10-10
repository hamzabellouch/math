import OAI.Analysis.LipschitzHilbert.Estimates.ChartPullback
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace OAI

/-! Reciprocal-Lipschitz dilation and its exact L2 scaling in the plane. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace LipschitzHilbert
open PacketRepresentation

theorem memLp_two_comp_smul_iff (f : Plane → ℂ) (hf : Continuous f)
    (L : ℝ) (hL : L≠0) :
    MemLp (fun x => f (L • x)) 2 volume ↔ MemLp f 2 volume := by
  have hc : Continuous (fun x => f (L • x)) := hf.comp (by fun_prop)
  constructor
  · intro h
    exact (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
      ((integrable_comp_smul_iff volume (fun x => ‖f x‖^2) hL).mp
        ((memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mp h))
  · intro h
    exact (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
      ((integrable_comp_smul_iff volume (fun x => ‖f x‖^2) hL).mpr
        ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp h))

theorem toLp_norm_comp_smul (f : Plane → ℂ) (hf : Continuous f) (hm : MemLp f 2 volume)
    (L : ℝ) (hL : 0<L) :
    ‖((memLp_two_comp_smul_iff f hf L hL.ne').mpr hm).toLp (fun x => f (L • x))‖=
      L⁻¹*‖hm.toLp f‖ := by
  have hmg := (memLp_two_comp_smul_iff f hf L hL.ne').mpr hm
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow,memLp_toL2_norm_sq volume _ hmg,memLp_toL2_norm_sq volume f hm,
    Measure.integral_comp_smul volume (fun x => ‖f x‖^2) L]
  simp only [Plane,finrank_euclideanSpace, Fintype.card_fin,smul_eq_mul]
  rw [abs_of_pos (inv_pos.mpr (pow_pos hL 2))]
  ring

def rescaleSchwartz (L : ℝ) (hL : L≠0) (f : SchwartzMap Plane ℂ) : SchwartzMap Plane ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ Plane L⁻¹ (inv_ne_zero hL)).toContinuousLinearEquiv f

@[simp] theorem rescaleSchwartz_apply (L : ℝ) (hL : L≠0) (f : SchwartzMap Plane ℂ) (x : Plane) :
    rescaleSchwartz L hL f x=f (L⁻¹ • x) := rfl

theorem rescaleSchwartz_norm (L : ℝ) (hL : 0<L) (f : SchwartzMap Plane ℂ) :
    ‖(rescaleSchwartz L hL.ne' f).toLp 2 volume‖=L*‖f.toLp 2 volume‖ := by
  have h := toLp_norm_comp_smul f f.continuous (f.memLp 2 volume) L⁻¹ (inv_pos.mpr hL)
  have hfun : (rescaleSchwartz L hL.ne' f : Plane → ℂ)=(fun x => f (L⁻¹ • x)) := by
    funext x
    rfl
  rw [Lp.norm_toLp] at h
  rw [SchwartzMap.norm_toLp]
  rw [hfun]
  simpa only [inv_inv,Lp.norm_toLp,SchwartzMap.norm_toLp] using h

theorem rescaleField_lipschitz_small {K : ℝ≥0} (hK : 0<K)
    {v : Plane → Plane} (hv : LipschitzWith K v) :
    LipschitzWith (1/100) (rescaleField (100*(K:ℝ)) v) := by
  have hKreal : 0<(K:ℝ) := hK
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (rescaleField (100*(K:ℝ)) v x) (rescaleField (100*(K:ℝ)) v y) ≤
        (K:ℝ)*dist ((100*(K:ℝ))⁻¹ • x) ((100*(K:ℝ))⁻¹ • y) := hv.dist_le_mul _ _
    _ = ((1/100 : ℝ≥0):ℝ)*dist x y := by
      rw [dist_smul₀,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (by positivity))]
      norm_num only [NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat]
      field_simp

theorem shortTransform_dilation (L : ℝ) (hL : L≠0) (v : Plane → Plane)
    (epsilon R : ℝ) (f : SchwartzMap Plane ℂ) :
    shortTransform (rescaleField L v) (L*epsilon) (L*R) (rescaleSchwartz L hL f)=
      fun x => shortTransform v epsilon R f (L⁻¹ • x) := by
  have hfun : (rescaleSchwartz L hL f : Plane → ℂ)=rescaleFunction L f := by
    funext x
    rfl
  rw [hfun]
  funext x
  have h := shortTransform_rescale hL v epsilon R f (L⁻¹ • x)
  simpa only [smul_smul,mul_inv_cancel₀ hL,one_smul] using h

end LipschitzHilbert

end

end OAI
