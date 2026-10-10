import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLevelInverse

namespace OAI

/-! The paired Mellin continuation at inverse rational cusps of a
primary modulus. It is derived from the actual theta transformation. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaLevelAxis (q x : Eisenstein) : ℝ → ℂ :=
  cubicThetaScaledAxis (3*(x:ℂ)/(q:ℂ)) (cubicThetaLevelScale q)

def cubicThetaLevelTail (q x : Eisenstein) (s : ℂ) : ℂ :=
  mellin (thetaUpper (cubicThetaLevelAxis q x)) s

def cubicThetaLevelCompleted (q x y : Eisenstein) (s : ℂ) : ℂ :=
  cubicThetaLevelTail q x s+cubicSymbol q (3*x)*cubicThetaLevelTail q y (-s)+
    cubicThetaLevelConstant q*(cubicSymbol q (3*x)/(s-2/3)-1/(s+2/3))

lemma cubicThetaLevelAxis_small {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) {t : ℝ} (ht : 0<t) :
    cubicThetaLevelAxis q x t=cubicSymbol q (3*x)*cubicThetaLevelAxis q y t⁻¹+
      cubicThetaLevelConstant q*(cubicSymbol q (3*x)*(t:ℂ)^(-(2/3:ℂ))-(t:ℂ)^(2/3:ℂ)) := by
  have he := cubicThetaLevelAxis_reciprocity hq y x
    (cubicThetaLevel_inverse_symmetric hxy) (inv_pos.mpr ht)
  rw [inv_inv] at he
  have hneg : cubicThetaScaledAxis (-3*(y:ℂ)/(q:ℂ)) (cubicThetaLevelScale q) t⁻¹=
      cubicThetaLevelAxis q y t⁻¹ := by
    unfold cubicThetaLevelAxis cubicThetaScaledAxis
    rw [neg_mul,neg_div,cubicThetaArithmetic_even]
  rw [hneg] at he
  have hp : ((t^(2/3:ℝ):ℝ):ℂ)=(t:ℂ)^(2/3:ℂ) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using Complex.ofReal_cpow ht.le (2/3:ℝ)
  have hi : (((t⁻¹)^(2/3:ℝ):ℝ):ℂ)=(t:ℂ)^(-(2/3:ℂ)) := by
    rw [Complex.ofReal_cpow (inv_nonneg.mpr ht.le),Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg ht.le,←Complex.cpow_neg]
    norm_num
  simpa only [cubicThetaLevelAxis,hp,hi] using he

lemma cubicThetaLevelAxis_decomposition {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) :
    cubicThetaLevelAxis q x =ᵐ[volume.restrict (Ioi 0)] fun t =>
      thetaUpper (cubicThetaLevelAxis q x) t+
        cubicSymbol q (3*x)*thetaUpper (cubicThetaLevelAxis q y) t⁻¹+
      cubicThetaLevelConstant q*(cubicSymbol q (3*x)*(Ioc (0:ℝ) 1).indicator
          (fun t : ℝ => (t:ℂ)^(-(2/3:ℂ))) t-
        (Ioc (0:ℝ) 1).indicator (fun t : ℝ => (t:ℂ)^(2/3:ℂ)) t) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi,
    (volume.restrict (Ioi 0)).ae_ne 1] with t ht ht1
  change 0<t at ht
  rcases lt_or_gt_of_ne ht1 with hlt | hgt
  · have hti : 1<t⁻¹ := (one_lt_inv₀ ht).mpr hlt
    simp only [thetaUpper,
      indicator_of_notMem (show t∉Ioi (1:ℝ) from not_lt.mpr hlt.le),
      indicator_of_mem (show t⁻¹∈Ioi (1:ℝ) from hti),zero_add,
      indicator_of_mem (show t∈Ioc (0:ℝ) 1 from ⟨ht,hlt.le⟩)]
    exact cubicThetaLevelAxis_small hq x y hxy ht
  · have hti : t⁻¹<1 := (inv_lt_one₀ ht).mpr hgt
    simp only [thetaUpper,indicator_of_mem (show t∈Ioi (1:ℝ) from hgt),
      indicator_of_notMem (show t⁻¹∉Ioi (1:ℝ) from not_lt.mpr hti.le),
      indicator_of_notMem (show t∉Ioc (0:ℝ) 1 from fun h => not_le_of_gt hgt h.2),
      add_zero,sub_self,mul_zero]

theorem cubicThetaLevelCompleted_mellin {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) {s : ℂ} (hs : 2/3<s.re) :
    mellin (cubicThetaLevelAxis q x) s=cubicThetaLevelCompleted q x y s := by
  have hU := cubicThetaScaledUpper_mellinConvergent (3*(x:ℂ)/(q:ℂ))
    (cubicThetaLevelScale_pos hq) s
  have hV := cubicThetaScaledUpper_mellinConvergent (3*(y:ℂ)/(q:ℂ))
    (cubicThetaLevelScale_pos hq) (-s)
  change MellinConvergent (thetaUpper (cubicThetaLevelAxis q x)) s at hU
  change MellinConvergent (thetaUpper (cubicThetaLevelAxis q y)) (-s) at hV
  have hI : MellinConvergent (fun t => thetaUpper (cubicThetaLevelAxis q y) t⁻¹) s := by
    have he : s/(-1:ℝ)= -s := by push_cast; ring
    rw [←he] at hV
    simpa only [Real.rpow_neg_one] using
      (MellinConvergent.comp_rpow (by norm_num : (-1:ℝ)≠0)).mpr hV
  have hSI := hasMellin_const_smul hI (cubicSymbol q (3*x))
  have hm := hasMellin_cpow_Ioc (-(2/3:ℂ)) (s:=s) (by norm_num; linarith)
  have hp := hasMellin_cpow_Ioc (2/3:ℂ) (s:=s) (by norm_num; linarith)
  have hSM := hasMellin_const_smul hm.1 (cubicSymbol q (3*x))
  have hD := hasMellin_sub hSM.1 hp.1
  have hC := hasMellin_const_smul hD.1 (cubicThetaLevelConstant q)
  have hSum := hasMellin_add (hasMellin_add hU hSI.1).1 hC.1
  simp only [smul_eq_mul] at hSI hSM hC hD hSum
  calc
    _ = mellin (fun t => thetaUpper (cubicThetaLevelAxis q x) t+
        cubicSymbol q (3*x)*thetaUpper (cubicThetaLevelAxis q y) t⁻¹+
      cubicThetaLevelConstant q*(cubicSymbol q (3*x)*(Ioc (0:ℝ) 1).indicator
          (fun t : ℝ => (t:ℂ)^(-(2/3:ℂ))) t-
        (Ioc (0:ℝ) 1).indicator (fun t : ℝ => (t:ℂ)^(2/3:ℂ)) t)) s := by
      apply integral_congr_ae
      filter_upwards [cubicThetaLevelAxis_decomposition hq x y hxy] with t ht
      rw [ht]
    _ = _ := by
      rw [hSum.2,(hasMellin_add hU hSI.1).2,hSI.2,hC.2,hD.2,hSM.2,hm.2,hp.2,mellin_comp_inv]
      simp only [cubicThetaLevelCompleted,cubicThetaLevelTail,sub_eq_add_neg,
        div_eq_mul_inv,one_mul]

theorem cubicThetaLevelCompleted_functional {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) (s : ℂ) :
    cubicThetaLevelCompleted q x y s=
      cubicSymbol q (3*x)*cubicThetaLevelCompleted q y x (-s) := by
  have hχ := cubicThetaLevel_inverse_phases hq hxy
  unfold cubicThetaLevelCompleted
  rw [neg_neg,show -s-2/3= -(s+2/3) by ring,show -s+2/3= -(s-2/3) by ring]
  simp only [div_neg]
  linear_combination
    -(cubicThetaLevelTail q x s-cubicThetaLevelConstant q/(s+2/3))*hχ

end CubicFirstMoment

end

end OAI
