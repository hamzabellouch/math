import Mathlib
import OAI.Analysis.Conductivity.Sources.AngularGraph

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

lemma ae_comp_of_nonzero_jacobian {f : Coord3 → Coord3}
    {D : Coord3 → Coord3 →L[ℝ] Coord3}
    (hf : ∀ x,HasFDerivAt f (D x) x) (hi : Function.Injective f)
    (hm : Measurable (fun x => ENNReal.ofReal |(D x).det|))
    (hn : ∀ x,(D x).det≠0) {P : Coord3 → Prop} (hP : ∀ᵐ y ∂volume,P y) :
    ∀ᵐ x ∂volume,P (f x) := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have he := map_withDensity_abs_det_fderiv_eq_addHaar (μ:=volume)
    (s:=univ) MeasurableSet.univ.nullMeasurableSet
    (fun x _ => (hf x).hasFDerivWithinAt) hi.injOn
  simp only [Measure.restrict_univ] at he
  have hp : ∀ᵐ y ∂Measure.map f (volume.withDensity (fun x => ENNReal.ofReal |(D x).det|)),P y := by
    rw [he]
    exact ae_restrict_of_ae hP
  have h := ae_of_ae_map hc.measurable.aemeasurable hp
  rw [ae_withDensity_iff hm] at h
  filter_upwards [h] with x hx
  exact hx (by simpa only [ne_eq,ENNReal.ofReal_eq_zero,abs_nonpos_iff] using hn x)

lemma faceRayAngle_injective {w : ℝ} (hw : 0<w) (i : Fin 4) :
    Function.Injective (faceRayAngle w i) :=
  (strictMono_of_hasDerivAt_pos (hasDerivAt_faceRayAngle w i)
    (faceRayDensity_pos' hw i)).injective

lemma sourceFaceAngles_injective (i j : Fin 4) : Function.Injective (sourceFaceAngles i j) := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [sourceFaceAngles,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at h0 h1 h2
  have hπ : 2*Real.pi≠0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have h1' := faceRayAngle_injective (by norm_num : (0:ℝ)<1) i (mul_left_cancel₀ hπ h1)
  have h2' := faceRayAngle_injective (by norm_num [sourceRadialWidth,sourceHole] : (0:ℝ)<sourceRadialWidth)
    j (mul_left_cancel₀ hπ h2)
  ext k
  fin_cases k <;> assumption

lemma sourceFaceAngles_ae {P : Coord3 → Prop} (hP : ∀ᵐ y ∂volume,P y) (i j : Fin 4) :
    ∀ᵐ x ∂volume,P (sourceFaceAngles i j x) := by
  apply ae_comp_of_nonzero_jacobian (sourceFaceAngles_hasFDeriv i j)
    (sourceFaceAngles_injective i j) _ _ hP
  · change Measurable (fun x : Coord3 => ENNReal.ofReal |(Matrix.toLin' (sourceFaceAngleMatrix i j x)).det|)
    simp only [LinearMap.det_toLin',sourceFaceAngleMatrix_det]
    exact (((continuous_const.mul ((continuous_faceRayDensity 1 i).comp (continuous_apply 1))).mul
      ((continuous_faceRayDensity sourceRadialWidth j).comp (continuous_apply 2))).abs.measurable.ennreal_ofReal)
  · intro x
    change (Matrix.toLin' (sourceFaceAngleMatrix i j x)).det≠0
    rw [LinearMap.det_toLin']
    rw [sourceFaceAngleMatrix_det]
    exact (mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one angularArea_ge_one)
      (faceRayDensity_pos' (by norm_num) i (x 1)))
      (faceRayDensity_pos' (by norm_num [sourceRadialWidth,sourceHole]) j (x 2))).ne'

end ScalarConductivity

end
end

end OAI
