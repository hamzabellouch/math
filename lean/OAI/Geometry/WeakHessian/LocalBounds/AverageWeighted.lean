import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.WeightedCZero
import OAI.Geometry.WeakHessian.LocalBounds.AverageLipschitz

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile118
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] [SigmaFinite m] in
lemma CurvatureDimension.cheegerHeat_average_weighted {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {V : X → ℝ} {L : ℝ≥0}
    (hV : LipschitzWith L V) (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    {t : ℝ} (ht : 0 < t) :
    MemLp (fun x => (t⁻¹ • ∫ s in 0..t,cheegerHeat h s u : Lp ℝ 2 m) x*Real.exp (V x)) 2 m ∧
      (∫ x,((t⁻¹ • ∫ s in 0..t,cheegerHeat h s u : Lp ℝ 2 m) x*Real.exp (V x))^2 ∂m) ≤
      (‖hU.toLp (fun x => u x*Real.exp (V x))‖*Real.exp ((L:ℝ)^2*t))^2 := by
  let C := ‖hU.toLp (fun x => u x*Real.exp (V x))‖*Real.exp ((L:ℝ)^2*t)
  have hi : IntervalIntegrable (fun s => cheegerHeat h s u) volume 0 t :=
    ((cheegerHeat_continuousOn hfin h u).mono (by rw [uIcc_of_le ht.le]; exact Icc_subset_Ici_self)).intervalIntegrable
  apply memLp_mul_exp_of_trunc hV.continuous.aestronglyMeasurable
  intro n
  let T := expMulLp (m := m) (hV.min_const (n:ℝ)).continuous.aestronglyMeasurable
    (ae_of_all _ (fun x => min_le_right (V x) (n:ℝ)))
  have hb (s : ℝ) (hs : s ∈ Ioc (0:ℝ) t) : ‖T (cheegerHeat h s u)‖ ≤ C := by
    have H := expMulLp_norm_le_weighted hV.continuous.aestronglyMeasurable (cheegerHeat h s u)
      (hcd.cheegerHeat_weighted hfin o h u hV hU hs.1.le).1 n
    exact H.trans ((hcd.cheegerHeat_weighted_norm hfin o h u hV hU hs.1.le).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 (sq_nonneg _))) (norm_nonneg _)))
  have H := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (f := fun s => T (cheegerHeat h s u)) (C := C) (fun s hs => by
      rw [uIoc_of_le ht.le] at hs
      exact hb s hs)
  rw [T.intervalIntegral_comp_comm hi,sub_zero,abs_of_pos ht] at H
  have Hav : ‖T (t⁻¹ • ∫ s in 0..t,cheegerHeat h s u)‖ ≤ C := by
    rw [map_smul,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos ht]
    calc t⁻¹ * ‖T (∫ s in 0..t,cheegerHeat h s u)‖ ≤ t⁻¹*(C*t) := mul_le_mul_of_nonneg_left H (by positivity)
         _ = C := by field_simp
  exact pow_le_pow_left₀ (norm_nonneg _) Hav 2

lemma RCD.cheegerHeat_average_compactDatum_CZero {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hfc : HasCompactSupport f) (hf2 : MemLp f 2 m)
    {t : ℝ} (ht : 0 < t) :
    ∃ g : X → ℝ,LipschitzWith (L*⟨Real.exp (|K| *t),(Real.exp_pos _).le⟩) g ∧
      g =ᵐ[m] (t⁻¹ • ∫ s in 0..t,cheegerHeat h s (hf2.toLp f) : Lp ℝ 2 m) ∧
      ∀ ε : ℝ,0 < ε → ∃ R : ℝ,0 ≤ R ∧ ∀ x : X,R < dist x o → |g x| < ε := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  obtain ⟨B,hB⟩ := hfc.isCompact_range hf.continuous |>.isBounded.exists_norm_le
  obtain ⟨g,hg,hge⟩ := hrcd.cheegerHeat_average_lipschitz hN hfull hfin h hf hf2
    (fun x => by simpa only [Real.norm_eq_abs] using hB (f x) ⟨x,rfl⟩) ht
  refine ⟨g,hg,hge,hrcd.1.lipschitz_vanishes_of_expWeighted hN hfull hfin o hg ?_⟩
  intro a ha
  have hV := lipschitz_mul_dist o a
  have hWf : MemLp (fun x => f x*Real.exp (a*dist x o)) 2 m :=
    (hf.continuous.mul (Real.continuous_exp.comp hV.continuous)).memLp_of_hasCompactSupport hfc.mul_right
  have hWu : MemLp (fun x => hf2.toLp f x*Real.exp (a*dist x o)) 2 m :=
    (memLp_congr_ae (hf2.coeFn_toLp.mul (Filter.EventuallyEq.rfl)).symm).mp hWf
  have H := (hrcd.1.cheegerHeat_average_weighted hfin o h (hf2.toLp f) hV hWu ht).1
  exact (memLp_congr_ae (hge.mul Filter.EventuallyEq.rfl).symm).mp H
end WeakHessian

end
end InlinedFile118

end OAI
