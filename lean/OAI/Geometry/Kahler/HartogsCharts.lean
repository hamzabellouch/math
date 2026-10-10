import OAI.Geometry.Kahler.HartogsJets

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

def baseCoordinateEquiv : Base ≃L[ℂ] (Fin 2 → ℂ) :=
  PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => ℂ)

def baseCoordinate (i : Fin 2) : Base →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj i).comp baseCoordinateEquiv.toContinuousLinearMap

@[simp] lemma baseCoordinate_apply (i : Fin 2) (z : Base) : baseCoordinate i z = z i := rfl

lemma centeredChart_analyticAt {r : ℝ} (U : Base ≃ₗᵢ[ℂ] Base) {z : Base}
    (hden : 1 + (r : ℂ) * z 0 ≠ 0) : AnalyticAt ℂ (centeredChart r U) z := by
  have h0 : AnalyticAt ℂ (fun z : Base => z 0) z := (baseCoordinate 0).analyticAt _
  have h1 : AnalyticAt ℂ (fun z : Base => z 1) z := (baseCoordinate 1).analyticAt _
  have hd : AnalyticAt ℂ (fun z : Base => 1 + (r : ℂ) * z 0) z := analyticAt_const.add (analyticAt_const.mul h0)
  have hv : AnalyticAt ℂ (fun z : Base => ![((r : ℂ) + z 0) / (1 + (r : ℂ) * z 0),
      (Real.sqrt (1-r^2) : ℂ) * z 1 / (1 + (r : ℂ) * z 0)]) z := by
    apply analyticAt_pi_iff.mpr
    intro i
    fin_cases i
    · exact (analyticAt_const.add h0).div hd hden
    · exact (analyticAt_const.mul h1).div hd hden
  exact (U.toContinuousLinearEquiv.analyticAt _).comp ((baseCoordinateEquiv.symm.analyticAt _).comp hv)

lemma centeredChart_zero (r : ℝ) (U : Base ≃ₗᵢ[ℂ] Base) :
    centeredChart r U 0 = U ((r : ℂ) • EuclideanSpace.single 0 1) := by
  unfold centeredChart
  congr 1
  ext i
  fin_cases i <;> simp

lemma centeredChart_zero_mem {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (U : Base ≃ₗᵢ[ℂ] Base) : centeredChart r U 0 ∈ ball := by
  rw [centeredChart_zero]
  simpa [ball, norm_smul, abs_of_nonneg hr] using hr1

lemma centeredChart_norm_identity {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (U : Base ≃ₗᵢ[ℂ] Base) (z : Base) (hd : 1 + (r : ℂ) * z 0 ≠ 0) :
    1 - ‖centeredChart r U z‖ ^ 2 =
      (1-r^2) * (1-‖z‖^2) / ‖1 + (r : ℂ) * z 0‖^2 := by
  have hsq : (Real.sqrt (1-r^2))^2 = 1-r^2 := Real.sq_sqrt (by nlinarith)
  have hdn : ‖1 + (r : ℂ) * z 0‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hd)
  simp only [centeredChart, LinearIsometryEquiv.norm_map, EuclideanSpace.norm_sq_eq,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    div_pow, mul_pow, sq_abs, hsq]
  field_simp [hdn]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
  ring

lemma centeredChart_den_ne_zero {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    {z : Base} (hz : z ∈ ball) : 1 + (r : ℂ) * z 0 ≠ 0 := by
  have hz0 := PiLp.norm_apply_le (p := (2 : ENNReal)) z 0
  have hnz : ‖z‖ < 1 := hz
  have hm : ‖(r : ℂ) * z 0‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    have := norm_nonneg (z 0)
    nlinarith
  intro he
  have hh : (r : ℂ) * z 0 = -1 := by linear_combination he
  rw [hh] at hm
  norm_num at hm

lemma centeredChart_mapsTo {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (U : Base ≃ₗᵢ[ℂ] Base) : MapsTo (centeredChart r U) ball ball := by
  intro z hz
  have hd := centeredChart_den_ne_zero hr hr1 hz
  have he := centeredChart_norm_identity hr hr1 U z hd
  have hpos : 0 < (1-r^2) * (1-‖z‖^2) / ‖1 + (r : ℂ)*z 0‖^2 := by
    apply div_pos
    · apply mul_pos <;> have hn : ‖z‖ < 1 := hz <;> nlinarith [norm_nonneg z]
    · exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hd)
  change ‖centeredChart r U z‖ < 1
  nlinarith [norm_nonneg (centeredChart r U z)]

lemma psi_centeredChart {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (U : Base ≃ₗᵢ[ℂ] Base) {z : Base} (hz : z ∈ ball) :
    psi (centeredChart r U z) = psi z - Real.log (1-r^2) +
      2 * (Complex.log (1+(r : ℂ)*z 0)).re := by
  have hd := centeredChart_den_ne_zero hr hr1 hz
  have hrp : 0 < 1-r^2 := by nlinarith
  have hzp : 0 < 1-‖z‖^2 := by have h : ‖z‖ < 1 := hz; nlinarith [norm_nonneg z]
  have hdp : ‖1+(r : ℂ)*z 0‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hd)
  simp only [psi, centeredChart_norm_identity hr hr1 U z hd, Complex.log_re,
    Real.log_div (mul_pos hrp hzp).ne' hdp, Real.log_mul hrp.ne' hzp.ne', Real.log_pow]
  ring

lemma exists_centeredChart {z : Base} (hz : z ∈ ball) :
    ∃ (r : ℝ) (U : Base ≃ₗᵢ[ℂ] Base), 0 ≤ r ∧ r < 1 ∧ centeredChart r U 0 = z := by
  classical
  by_cases hz0 : z = 0
  · subst z
    exact ⟨0, LinearIsometryEquiv.refl ℂ Base, by norm_num, by norm_num,
      by simp [centeredChart_zero]⟩
  let v : Base := (‖z‖⁻¹ : ℂ) • z
  have hv : ‖v‖ = 1 := by
    simp [v, norm_smul, norm_ne_zero_iff.mpr hz0]
  have ho : Orthonormal ℂ (({0} : Set (Fin 2)).domRestrict (fun _ : Fin 2 => v)) := by
    constructor
    · intro i
      exact hv
    · intro i j hij
      exact (hij (Subsingleton.elim _ _)).elim
  obtain ⟨b, hb⟩ := ho.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨‖z‖, b.repr.symm, norm_nonneg _, hz, ?_⟩
  rw [centeredChart_zero, map_smul, b.repr_symm_single, hb 0 (by simp)]
  dsimp [v]
  rw [← Complex.coe_smul, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz0)), one_smul]

lemma fderiv_centeredChart_zero (r : ℝ) (U : Base ≃ₗᵢ[ℂ] Base) (u : Base) :
    fderiv ℂ (centeredChart r U) 0 u =
      U (WithLp.toLp 2 ![(1-(r : ℂ)^2)*u 0, (Real.sqrt (1-r^2) : ℂ)*u 1]) := by
  have hG : HasDerivAt (fun y : ℂ => ((r : ℂ)+y)/(1+(r : ℂ)*y))
      (1-(r : ℂ)^2) 0 := by
    convert ((hasDerivAt_const 0 (r : ℂ)).add (hasDerivAt_id 0)).div
      ((hasDerivAt_const 0 (1 : ℂ)).add ((hasDerivAt_id 0).const_mul (r : ℂ))) (by simp) using 1 <;> try rfl
    simp
    ring
  have h0 : HasFDerivAt (fun z : Base => ((r : ℂ)+z 0)/(1+(r : ℂ)*z 0))
      ((1-(r : ℂ)^2) • baseCoordinate 0) 0 := by
    have hg : HasDerivAt (fun y : ℂ => ((r : ℂ)+y)/(1+(r : ℂ)*y))
        (1-(r : ℂ)^2) ((baseCoordinate 0) (0 : Base)) := by simpa using hG
    exact hg.comp_hasFDerivAt (0 : Base) (baseCoordinate 0).hasFDerivAt
  have hden : DifferentiableAt ℂ (fun z : Base => (1+(r : ℂ)*z 0)⁻¹) 0 :=
    ((analyticAt_const.add (analyticAt_const.mul ((baseCoordinate 0).analyticAt 0))).inv (by simp)).differentiableAt
  have h1 : HasFDerivAt (fun z : Base => (Real.sqrt (1-r^2) : ℂ)*z 1/(1+(r : ℂ)*z 0))
      ((Real.sqrt (1-r^2) : ℂ) • baseCoordinate 1) 0 := by
    have hA : HasFDerivAt (fun z : Base => (Real.sqrt (1-r^2) : ℂ) * z 1)
        ((Real.sqrt (1-r^2) : ℂ) • baseCoordinate 1) (0 : Base) :=
      (baseCoordinate 1).hasFDerivAt.const_mul _
    have hB : HasFDerivAt (fun z : Base => (1+(r : ℂ)*z 0)⁻¹)
        (fderiv ℂ (fun z : Base => (1+(r : ℂ)*z 0)⁻¹) 0) (0 : Base) := hden.hasFDerivAt
    have hh : HasFDerivAt
        (fun z : Base => ((Real.sqrt (1-r^2) : ℂ)*z 1) * (1+(r : ℂ)*z 0)⁻¹)
        (((Real.sqrt (1-r^2) : ℂ) * (0 : Base) 1) • fderiv ℂ (fun z : Base => (1+(r : ℂ)*z 0)⁻¹) 0 +
          (1+(r : ℂ)*(0 : Base) 0)⁻¹ • ((Real.sqrt (1-r^2) : ℂ) • baseCoordinate 1))
        (0 : Base) := hA.mul hB
    have hh' := hh.congr_fderiv (show
        (((Real.sqrt (1-r^2) : ℂ) * (0 : Base) 1) • fderiv ℂ (fun z : Base => (1+(r : ℂ)*z 0)⁻¹) 0 +
          (1+(r : ℂ)*(0 : Base) 0)⁻¹ • ((Real.sqrt (1-r^2) : ℂ) • baseCoordinate 1)) =
        ((Real.sqrt (1-r^2) : ℂ) • baseCoordinate 1) by
      ext z
      simp)
    simpa only [div_eq_mul_inv] using hh'
  have hp : HasFDerivAt (fun z : Base => ![((r : ℂ)+z 0)/(1+(r : ℂ)*z 0),
      (Real.sqrt (1-r^2) : ℂ)*z 1/(1+(r : ℂ)*z 0)])
      (ContinuousLinearMap.pi ![(1-(r : ℂ)^2) • baseCoordinate 0,
        (Real.sqrt (1-r^2) : ℂ) • baseCoordinate 1]) 0 := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact h0
    · exact h1
  have hh := U.toContinuousLinearEquiv.hasFDerivAt.comp 0
    (baseCoordinateEquiv.symm.hasFDerivAt.comp 0 hp)
  change HasFDerivAt (centeredChart r U) _ 0 at hh
  rw [hh.fderiv]
  change U (baseCoordinateEquiv.symm _) = U _
  congr 1
  ext i
  fin_cases i <;> rfl

lemma fderiv_centeredChart_zero_injective {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (U : Base ≃ₗᵢ[ℂ] Base) : Function.Injective (fderiv ℂ (centeredChart r U) 0) := by
  have hpos : 0 < 1-r^2 := by nlinarith
  have h0 : (1-(r : ℂ)^2) ≠ 0 := by exact_mod_cast hpos.ne'
  have h1 : (Real.sqrt (1-r^2) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
  intro u v huv
  rw [fderiv_centeredChart_zero, fderiv_centeredChart_zero] at huv
  have he := U.injective huv
  have ha := congrArg (fun z : Base => z 0) he
  have hb := congrArg (fun z : Base => z 1) he
  ext i
  fin_cases i
  · exact mul_left_cancel₀ h0 ha
  · exact mul_left_cancel₀ h1 hb

end PinchedHartogs

end

end OAI
