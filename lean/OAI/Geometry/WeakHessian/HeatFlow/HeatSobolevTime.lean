import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.CheegerEnergyConst
import OAI.Geometry.WeakHessian.Sobolev.GlobalCheegerEnergyWeak
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatContinuous

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile101
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma convex_upperGradient_sublevel (B : ℝ) :
    Convex ℝ {f : Lp ℝ 2 m | ∃ D : Lp ℝ 2 m, IsLocalWeakUpperGradient m f D ∧ ‖D‖ ≤ B} := by
  rintro u ⟨D,hD,hDB⟩ v ⟨E,hE,hEB⟩ a b ha hb hab
  refine ⟨a • D+b • E, ?_, ?_⟩
  · exact convex_l2GradientGraph (x := WithLp.toLp 2 (u,D)) (y := WithLp.toLp 2 (v,E)) hD hE ha hb hab
  · calc
      ‖a • D+b • E‖ ≤ ‖a • D‖+‖b • E‖ := norm_add_le _ _
      _ = a*‖D‖+b*‖E‖ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb]
      _ ≤ a*B+b*B := add_le_add (mul_le_mul_of_nonneg_left hDB ha) (mul_le_mul_of_nonneg_left hEB hb)
      _ = B := by rw [← add_mul,hab,one_mul]

lemma CurvatureDimension.cheegerHeat_upperGradient_norm {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m) (o : X)
    {u D : Lp ℝ 2 m} (hD : IsLocalWeakUpperGradient m u D) {t : ℝ} (ht : 0 ≤ t) :
    ∃ E : Lp ℝ 2 m, IsLocalWeakUpperGradient m (cheegerHeat h t u) E ∧ ‖E‖ ≤ ‖D‖ := by
  have he := (cheegerHeat_energy_le h ht u).trans (hcd.global_cheegerEnergy_le_weak hfin o hD)
  obtain ⟨E,hE,hEn⟩ := exists_minimalGradient_energy_le_cheeger hfin (Lp.memLp (cheegerHeat h t u))
    (he.trans_lt ENNReal.ofReal_lt_top)
  have hs := ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ ‖D‖^2/2) |>.mp (hEn.trans he)
  refine ⟨E,hE.1,?_⟩
  exact le_of_sq_le_sq
    ((div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mp hs) (norm_nonneg D)

lemma CurvatureDimension.cheegerHeat_difference_upperGradient {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m) (o : X)
    {u A D : Lp ℝ 2 m} (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hD : IsLocalWeakUpperGradient m A D) {t : ℝ} (ht : 0 < t) :
    ∃ E : Lp ℝ 2 m, IsLocalWeakUpperGradient m (cheegerHeat h t u-u : Lp ℝ 2 m) E ∧ ‖E‖ ≤ t*‖D‖ := by
  have havg := (convex_upperGradient_sublevel (m := m) ‖D‖).set_average_mem
    (isClosed_upperGradient_sublevel ‖D‖)
    (show volume (Ioc (0:ℝ) t) ≠ 0 by simp [ht])
    (show volume (Ioc (0:ℝ) t) ≠ ∞ by simp)
    (show ∀ᵐ s ∂volume.restrict (Ioc (0:ℝ) t),
      ∃ E : Lp ℝ 2 m, IsLocalWeakUpperGradient m (cheegerHeat h s A) E ∧ ‖E‖ ≤ ‖D‖ from
        (ae_restrict_mem measurableSet_Ioc).mono fun s hs => hcd.cheegerHeat_upperGradient_norm hfin h o hD hs.1.le)
    (((cheegerHeat_continuousOn hfin h A).mono (show Icc 0 t ⊆ Ici 0 from Icc_subset_Ici_self)).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  rcases havg with ⟨E,hE,hEn⟩
  have heq : t • (⨍ s in Ioc (0:ℝ) t,cheegerHeat h s A) = cheegerHeat h t u-u := by
    rw [average_eq,measureReal_def,Measure.restrict_apply_univ,Real.volume_Ioc,sub_zero,ENNReal.toReal_ofReal ht.le]
    rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
    rw [← intervalIntegral.integral_of_le ht.le]
    exact cheegerHeat_integral_generator hfin h hu ht.le
  refine ⟨t • E,?_,?_⟩
  · have HH := hE.const_mul t
    apply HH.congr_ae
    · filter_upwards [Lp.coeFn_smul t (⨍ s in Ioc (0:ℝ) t,cheegerHeat h s A)] with x hx
      simpa only [heq,Pi.smul_apply,smul_eq_mul] using hx.symm
    · filter_upwards [Lp.coeFn_smul t E] with x hx
      simpa only [abs_of_pos ht,Pi.smul_apply,smul_eq_mul] using hx.symm
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    exact mul_le_mul_of_nonneg_left hEn ht.le
end WeakHessian

end
end InlinedFile101

end OAI
