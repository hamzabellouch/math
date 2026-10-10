import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticCuspEnergy
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticCuspMass

namespace OAI

/-! The actual gradient energy of the arithmetic remainder is integrable
in every cusp, with the same convergent vertical power as its mass. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaArithmeticCoordinateEnergy (δ : SL(2,Eisenstein)) (s : ℂ) (hs : 2<s.re)
    (y : ℂ × ℝ) : ℝ :=
  cubicThetaSectionEnergy (cubicThetaArithmeticSection s hs) (δ • cubicThetaPointInclusion.symm y)

lemma cubicThetaArithmeticCoordinateEnergy_apply (δ : SL(2,Eisenstein))
    (s : ℂ) (hs : 2<s.re) (p : CubicThetaPoint) :
    cubicThetaArithmeticCoordinateEnergy δ s hs (cubicThetaPointCoordinates p)=
      cubicThetaSectionEnergy (cubicThetaArithmeticSection s hs) (δ • p) := by
  have h : cubicThetaPointInclusion.symm (cubicThetaPointCoordinates p)=p :=
    cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)
  simp only [cubicThetaArithmeticCoordinateEnergy,h]

lemma cubicThetaArithmeticCoordinateEnergy_density_bound (δ : SL(2,Eisenstein))
    {s : ℂ} (hs : 3<s.re) {y : ℂ × ℝ} (hy : 2<y.2) {R : ℝ}
    (hR : Complex.normSq y.1≤R) :
    cubicThetaArithmeticCoordinateEnergy δ s (by linarith) y/y.2^3≤
      ((Module.finrank ℝ CubicThetaTangent:ℝ)*
        (6*(3+2*R)^2*cubicThetaFirstJetConstant s*cubicThetaCuspLatticeMass s)^2)*y.2^(5-2*s.re) := by
  have hy0 : 0<y.2 := by linarith
  let p : CubicThetaPoint := ⟨y,hy0⟩
  let A := 6*(3+2*R)^2*cubicThetaFirstJetConstant s*cubicThetaCuspLatticeMass s
  let D := (Module.finrank ℝ CubicThetaTangent:ℝ)
  have hD : 0≤D := Nat.cast_nonneg _
  have hb := cubicThetaArithmeticCusp_fderiv_bound δ hs hy hR
  have hb' : ‖fderiv ℝ (fun q => cubicThetaArithmeticRemainder
      (cubicThetaMobius (cubicThetaFullComplex δ) q) s) y‖≤A*y.2^(3-s.re) := by
    exact hb.trans_eq (by dsimp [A]; ring)
  have hsq := mul_self_le_mul_self (_root_.norm_nonneg _) hb'
  simp only [← pow_two] at hsq
  have he : (y.2^(3-s.re))^2/y.2=y.2^(5-2*s.re) := by
    rw [← Real.rpow_mul_natCast hy0.le,← Real.rpow_sub_one hy0.ne']
    congr 1
    norm_num
    ring
  have hec := cubicThetaArithmeticCusp_energy_le δ (s:=s) (by linarith) p
  have hec' : cubicThetaArithmeticCoordinateEnergy δ s (by linarith) y≤
      D*y.2^2*(A*y.2^(3-s.re))^2 := by
    change cubicThetaArithmeticCoordinateEnergy δ s (by linarith) (cubicThetaPointCoordinates p)≤_
    rw [cubicThetaArithmeticCoordinateEnergy_apply]
    exact hec.trans (mul_le_mul_of_nonneg_left hsq (mul_nonneg hD (sq_nonneg _)))
  calc
    _ ≤ (D*y.2^2*(A*y.2^(3-s.re))^2)/y.2^3 :=
      div_le_div_of_nonneg_right hec' (pow_nonneg hy0.le 3)
    _ = D*A^2*((y.2^(3-s.re))^2/y.2) := by field_simp [hy0.ne']
    _ = _ := by rw [he]

lemma cubicThetaArithmeticCoordinateEnergy_density_continuousOn (δ : SL(2,Eisenstein))
    (s : ℂ) (hs : 2<s.re) :
    ContinuousOn (fun y => cubicThetaArithmeticCoordinateEnergy δ s hs y/y.2^3)
      (cubicThetaHorizontalCell ×ˢ Ioi (2:ℝ)) := by
  intro y hy
  have hy0 : 0<y.2 := lt_trans (by norm_num : (0:ℝ)<2) hy.2
  have hi : ContinuousAt (fun y => cubicThetaPointInclusion.symm y) y :=
    cubicThetaPointInclusion.symm.continuousAt (by
      change y ∈ cubicThetaPointInclusion.target
      rw [cubicThetaPointInclusion_target]
      exact hy0)
  have he := (cubicThetaArithmeticEnergy_continuous hs).continuousAt.comp
    ((continuous_const_smul δ).continuousAt.comp hi)
  exact (he.div (continuousAt_snd.pow 3) (pow_ne_zero 3 hy0.ne')).continuousWithinAt

theorem cubicThetaArithmeticCoordinateEnergy_integrable (δ : SL(2,Eisenstein))
    {s : ℂ} (hs : 3<s.re) :
    IntegrableOn (fun y => cubicThetaArithmeticCoordinateEnergy δ s (by linarith) y/y.2^3)
      (cubicThetaHorizontalCell ×ˢ Ioi (2:ℝ)) := by
  obtain ⟨R,_,hR⟩ := cubicThetaHorizontalCell_normSq_bound
  let C := (Module.finrank ℝ CubicThetaTangent:ℝ)*
    (6*(3+2*R)^2*cubicThetaFirstJetConstant s*cubicThetaCuspLatticeMass s)^2
  have hh : IntegrableOn (fun _ : ℂ => C) cubicThetaHorizontalCell :=
    integrableOn_const cubicThetaHorizontalCell_measure_ne_top
  have hv : IntegrableOn (fun v : ℝ => v^(5-2*s.re)) (Ioi (2:ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hm := hh.mul_prod hv
  rw [Measure.prod_restrict] at hm
  apply hm.mono'
  · exact (cubicThetaArithmeticCoordinateEnergy_density_continuousOn δ s (by linarith)).aestronglyMeasurable
      (cubicThetaHorizontalCell_measurable.prod measurableSet_Ioi)
  · filter_upwards [ae_restrict_mem (cubicThetaHorizontalCell_measurable.prod measurableSet_Ioi)] with y hy
    have hn : 0≤cubicThetaArithmeticCoordinateEnergy δ s (by linarith) y :=
      mul_nonneg (sq_nonneg _) (cubicThetaTangentEnergy_nonneg _)
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg hn
      (pow_nonneg (lt_trans (by norm_num : (0:ℝ)<2) hy.2).le 3))]
    exact cubicThetaArithmeticCoordinateEnergy_density_bound δ hs hy.2 (hR y.1 hy.1)

end CubicFirstMoment

end

end OAI
