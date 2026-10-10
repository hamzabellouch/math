import Mathlib
import OAI.Probability.SKBarriers.Parisi.QuantileTransport

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem unitCDF_mul_indicator (q : ℝ) (f : ℝ → ℝ) :
    (fun x => unitCDF q x*f x)=(Ici q).indicator f := by
  funext x
  simp only [unitCDF,Set.indicator_apply,mem_Ici]
  split_ifs <;> simp

theorem unitCDF_mul_integrable (q : ℝ) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc (0:ℝ) 1)) :
    IntegrableOn (fun x => unitCDF q x*f x) (Icc (0:ℝ) 1) := by
  rw [unitCDF_mul_indicator]
  exact hf.indicator measurableSet_Ici

theorem unitCDF_mul_integral (q : ℝ) (hq : q∈Icc (0:ℝ) 1) (f : ℝ → ℝ) :
    (∫ x in Icc (0:ℝ) 1, unitCDF q x*f x)=∫ x in q..1, f x := by
  rw [unitCDF_mul_indicator,setIntegral_indicator measurableSet_Ici]
  have he : Icc (0:ℝ) 1∩Ici q=Icc q 1 := by
    ext x
    simp only [mem_inter_iff,mem_Icc,mem_Ici]
    constructor
    · intro H; exact ⟨H.2,H.1.2⟩
    · intro H; exact ⟨⟨hq.1.trans H.1,H.2⟩,H.1⟩
  rw [he,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hq.2]

theorem unitCDF_sub_mul_integral (a b : ℝ) (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1)
    {f : ℝ → ℝ} (hf : IntegrableOn f (Icc (0:ℝ) 1)) :
    (∫ x in Icc (0:ℝ) 1, (unitCDF b x-unitCDF a x)*f x)=-(∫ x in a..b, f x) := by
  simp_rw [sub_mul]
  rw [integral_sub (unitCDF_mul_integrable b hf) (unitCDF_mul_integrable a hf),
    unitCDF_mul_integral b hb,unitCDF_mul_integral a ha]
  have h01 : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0:ℝ)≤1)).mpr hf
  have ha1 : IntervalIntegrable f volume a 1 := h01.mono_set (by
    rw [uIcc_of_le ha.2,uIcc_of_le (by norm_num : (0:ℝ)≤1)]
    intro x hx; exact ⟨ha.1.trans hx.1,hx.2⟩)
  have hb1 : IntervalIntegrable f volume b 1 := h01.mono_set (by
    rw [uIcc_of_le hb.2,uIcc_of_le (by norm_num : (0:ℝ)≤1)]
    intro x hx; exact ⟨hb.1.trans hx.1,hx.2⟩)
  have H := intervalIntegral.integral_interval_sub_left hb1.symm ha1.symm
  rw [intervalIntegral.integral_symm (f:=f) (a:=b) (b:=1),
    intervalIntegral.integral_symm (f:=f) (a:=a) (b:=1)] at H
  linarith

theorem quantileCDF_signed_transport {k : ℕ} (A B : Fin (k+1) → ℝ)
    (hA : ∀ j, A j∈Icc (0:ℝ) 1) (hB : ∀ j, B j∈Icc (0:ℝ) 1)
    {f : ℝ → ℝ} (hf : IntegrableOn f (Icc (0:ℝ) 1)) :
    (∫ x in Icc (0:ℝ) 1, (quantileCDF k B x-quantileCDF k A x)*f x)=
      -∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(∫ x in A j..B j, f x) := by
  have he (x : ℝ) : (quantileCDF k B x-quantileCDF k A x)*f x=
      ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*((unitCDF (B j) x-unitCDF (A j) x)*f x) := by
    rw [quantileCDF_eq_unitCDF_sum,quantileCDF_eq_unitCDF_sum,← mul_sub,
      ← Finset.sum_sub_distrib,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _; ring
  simp_rw [he]
  have hi (j : Fin (k+1)) : IntegrableOn (fun x => (unitCDF (B j) x-unitCDF (A j) x)*f x) (Icc (0:ℝ) 1) := by
    simp_rw [sub_mul]
    exact (unitCDF_mul_integrable (B j) hf).sub (unitCDF_mul_integrable (A j) hf)
  rw [integral_finsetSum _ (fun j _ => (hi j).const_mul _)]
  simp_rw [integral_const_mul,unitCDF_sub_mul_integral _ _ (hA _) (hB _) hf,mul_neg]
  rw [Finset.sum_neg_distrib]

end SK.Analytic

end
end

end OAI
