import OAI.NumberTheory.CubicMoment.Theta.CubicThetaNormalizedSeries
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMellin

namespace OAI

/-! Mellin continuation of the actual arithmetic theta expansion.
The undetermined constant-to-Fourier ratio remains visible in both residues. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaArithmeticAxis (v : ℝ) : ℂ :=
  cubicThetaNonconstant cubicThetaArithmeticCoefficient (0,v)

def cubicThetaArithmeticTail (s : ℂ) : ℂ :=
  mellin (thetaUpper cubicThetaArithmeticAxis) s

def cubicThetaArithmeticCompleted (s : ℂ) : ℂ :=
  cubicThetaArithmeticTail s+cubicThetaArithmeticTail (-s)+
    cubicThetaSeriesConstant*(1/(s-2/3)-1/(s+2/3))

lemma cubicThetaArithmeticAxis_small {v : ℝ} (hv : 0<v) :
    cubicThetaArithmeticAxis v=cubicThetaArithmeticAxis v⁻¹+
      cubicThetaSeriesConstant*((v:ℂ)^(-(2/3:ℂ))-(v:ℂ)^(2/3:ℂ)) := by
  have hp : ((v^(2/3:ℝ):ℝ):ℂ)=(v:ℂ)^(2/3:ℂ) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using
      Complex.ofReal_cpow hv.le (2/3:ℝ)
  have hi : (((v⁻¹)^(2/3:ℝ):ℝ):ℂ)=(v:ℂ)^(-(2/3:ℂ)) := by
    rw [Complex.ofReal_cpow (inv_nonneg.mpr hv.le),Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg hv.le,←Complex.cpow_neg]
    norm_num
  simpa only [cubicThetaArithmeticAxis,hp,hi] using cubicThetaArithmetic_center_small hv

lemma cubicThetaArithmeticAxis_decomposition :
    cubicThetaArithmeticAxis =ᵐ[volume.restrict (Ioi 0)]
      fun v => thetaUpper cubicThetaArithmeticAxis v+thetaUpper cubicThetaArithmeticAxis v⁻¹+
        cubicThetaSeriesConstant*((Ioc (0:ℝ) 1).indicator
          (fun t : ℝ => (t:ℂ)^(-(2/3:ℂ))) v-
            (Ioc (0:ℝ) 1).indicator (fun t : ℝ => (t:ℂ)^(2/3:ℂ)) v) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi,
    (volume.restrict (Ioi 0)).ae_ne 1] with v hv hv1
  change 0<v at hv
  rcases lt_or_gt_of_ne hv1 with hlt | hgt
  · have hvi : 1<v⁻¹ := (one_lt_inv₀ hv).mpr hlt
    simp only [thetaUpper,indicator_of_notMem (show v∉Ioi (1:ℝ) from not_lt.mpr hlt.le),
      indicator_of_mem (show v⁻¹∈Ioi (1:ℝ) from hvi),zero_add,
      indicator_of_mem (show v∈Ioc (0:ℝ) 1 from ⟨hv,hlt.le⟩)]
    exact cubicThetaArithmeticAxis_small hv
  · have hvi : v⁻¹<1 := (inv_lt_one₀ hv).mpr hgt
    simp only [thetaUpper,indicator_of_mem (show v∈Ioi (1:ℝ) from hgt),
      indicator_of_notMem (show v⁻¹∉Ioi (1:ℝ) from not_lt.mpr hvi.le),
      indicator_of_notMem (show v∉Ioc (0:ℝ) 1 from fun h => not_le_of_gt hgt h.2),
      add_zero,sub_self,mul_zero]

theorem cubicThetaArithmeticCompleted_mellin {s : ℂ} (hs : 2/3<s.re) :
    mellin cubicThetaArithmeticAxis s=cubicThetaArithmeticCompleted s := by
  have hU := cubicTheta_upper_mellinConvergent (by norm_num : (0:ℝ)≤81)
    cubicThetaArithmeticCoefficient_bound 0 s
  have hV := cubicTheta_upper_mellinConvergent (by norm_num : (0:ℝ)≤81)
    cubicThetaArithmeticCoefficient_bound 0 (-s)
  change MellinConvergent (thetaUpper cubicThetaArithmeticAxis) s at hU
  change MellinConvergent (thetaUpper cubicThetaArithmeticAxis) (-s) at hV
  have hI : MellinConvergent (fun v => thetaUpper cubicThetaArithmeticAxis v⁻¹) s := by
    have he : s/(-1:ℝ)= -s := by push_cast; ring
    rw [←he] at hV
    simpa only [Real.rpow_neg_one] using
      (MellinConvergent.comp_rpow (by norm_num : (-1:ℝ)≠0)).mpr hV
  have hm := hasMellin_cpow_Ioc (-(2/3:ℂ)) (s:=s) (by norm_num; linarith)
  have hp := hasMellin_cpow_Ioc (2/3:ℂ) (s:=s) (by norm_num; linarith)
  have hD := hasMellin_sub hm.1 hp.1
  have hC := hasMellin_const_smul hD.1 cubicThetaSeriesConstant
  have hSum := hasMellin_add (hasMellin_add hU hI).1 hC.1
  simp only [smul_eq_mul] at hC hSum
  calc
    mellin cubicThetaArithmeticAxis s = mellin (fun v =>
        thetaUpper cubicThetaArithmeticAxis v+thetaUpper cubicThetaArithmeticAxis v⁻¹+
          cubicThetaSeriesConstant*((Ioc (0:ℝ) 1).indicator
            (fun t : ℝ => (t:ℂ)^(-(2/3:ℂ))) v-
              (Ioc (0:ℝ) 1).indicator (fun t : ℝ => (t:ℂ)^(2/3:ℂ)) v)) s := by
      apply integral_congr_ae
      filter_upwards [cubicThetaArithmeticAxis_decomposition] with v hv
      rw [hv]
    _ = _ := by
      rw [hSum.2,(hasMellin_add hU hI).2,hC.2,hD.2,hm.2,hp.2,mellin_comp_inv]
      simp only [cubicThetaArithmeticCompleted,cubicThetaArithmeticTail,sub_eq_add_neg]

theorem cubicThetaArithmeticCompleted_even (s : ℂ) :
    cubicThetaArithmeticCompleted (-s)=cubicThetaArithmeticCompleted s := by
  unfold cubicThetaArithmeticCompleted
  rw [neg_neg,show -s-2/3= -(s+2/3) by ring,show -s+2/3= -(s-2/3) by ring]
  simp only [div_neg]
  ring

theorem cubicThetaArithmeticCompleted_dirichlet {s : ℂ} (hs : 2<s.re) :
    cubicThetaArithmeticCompleted s=
      mellin cubicThetaWhittaker s*cubicThetaDirichlet cubicThetaArithmeticCoefficient s := by
  rw [←cubicThetaArithmeticCompleted_mellin (by linarith)]
  exact cubicThetaNonconstant_mellin (by norm_num) cubicThetaArithmeticCoefficient_norm_le hs

end CubicFirstMoment

end

end OAI
