import Mathlib
import OAI.Geometry.WeakHessian.Curvature.DecayWeight
import OAI.Geometry.WeakHessian.LocalBounds.IdentifiedConservation

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] in
lemma norm_toLp_le_scaled {f g : X → ℝ} (hf : MemLp f 2 m) (hg : MemLp g 2 m)
    {C : ℝ} (hC : 0 ≤ C) (hfg : ∀ᵐ x ∂m, |f x| ≤ C*|g x|) :
    ‖hf.toLp f‖ ≤ C*‖hg.toLp g‖ := by
  calc
    _ ≤ ‖C • hg.toLp g‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp,Lp.coeFn_smul C (hg.toLp g),hfg]
        with x hf hg hs hx
      simp only [hf,hs,Pi.smul_apply,smul_eq_mul,hg,Real.norm_eq_abs,abs_mul,abs_of_nonneg hC]
      exact hx
    _ = _ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hC]

lemma supported_exp_weight_norm (u : Lp ℝ 2 m) {β : ℝ} (hβ : 0 ≤ β)
    (o : X) {r : ℝ} (hsupp : ∀ᵐ x ∂m,r ≤ dist x o → u x = 0) :
    ‖(memLp_exp_dist_of_support u hβ o hsupp).toLp
      (fun x => u x*Real.exp (β*dist x o))‖ ≤ Real.exp (β*r)*‖u‖ := by
  have H := norm_toLp_le_scaled (memLp_exp_dist_of_support u hβ o hsupp) (Lp.memLp u)
    (Real.exp_pos (β*r)).le (show ∀ᵐ x ∂m,
      |u x*Real.exp (β*dist x o)| ≤ Real.exp (β*r)*|u x| from by
      filter_upwards [hsupp] with x hx
      by_cases hr : r ≤ dist x o
      · simp only [hx hr,zero_mul,abs_zero,mul_zero,le_refl]
      · rw [abs_mul,abs_of_pos (Real.exp_pos _),mul_comm]
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (le_of_not_ge hr) hβ)) (abs_nonneg _))
  simpa using H

lemma tail_exp_weight (o : X) {c β R : ℝ} (hcβ : c ≤ β)
    (hd : MemLp (fun x => Real.exp (-c*dist x o)) 2 m) :
    MemLp (fun x => Real.exp (-(β*dist x o))*
      (Ici R).indicator (fun _ : ℝ => (1:ℝ)) (dist x o)) 2 m := by
  let C := Real.exp (-(β-c)*R)
  have hm : Measurable (fun x : X => (Ici R).indicator (fun _ : ℝ => (1:ℝ)) (dist x o)) :=
    (measurable_const.indicator measurableSet_Ici).comp (continuous_id.dist continuous_const).measurable
  apply (hd.const_mul C).mono
    ((show Continuous (fun x : X => Real.exp (-(β*dist x o))) by fun_prop).aestronglyMeasurable.mul hm.aestronglyMeasurable)
  exact ae_of_all _ fun x => by
    change |Real.exp (-(β*dist x o))*(Ici R).indicator (fun _ : ℝ => (1:ℝ)) (dist x o)| ≤
      |C*Real.exp (-c*dist x o)|
    by_cases hR : R ≤ dist x o
    · rw [indicator_of_mem (show dist x o ∈ Ici R from hR),mul_one,abs_of_pos (Real.exp_pos _),abs_of_pos (by dsimp [C]; positivity)]
      dsimp [C]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hcβ) (sub_nonneg.mpr hR)]
    · rw [indicator_of_notMem (show dist x o ∉ Ici R from hR),mul_zero,abs_zero]
      exact abs_nonneg _

lemma tail_exp_weight_norm (o : X) {c β R : ℝ} (hcβ : c ≤ β)
    (hd : MemLp (fun x => Real.exp (-c*dist x o)) 2 m) :
    ‖(tail_exp_weight o hcβ hd (R := R)).toLp (fun x => Real.exp (-(β*dist x o))*
      (Ici R).indicator (fun _ : ℝ => (1:ℝ)) (dist x o))‖ ≤
      Real.exp (-(β-c)*R)*‖hd.toLp (fun x => Real.exp (-c*dist x o))‖ := by
  apply norm_toLp_le_scaled _ hd (Real.exp_pos _).le
  exact ae_of_all _ fun x => by
    by_cases hR : R ≤ dist x o
    · rw [indicator_of_mem (show dist x o ∈ Ici R from hR),mul_one,abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _),← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hcβ) (sub_nonneg.mpr hR)]
    · rw [indicator_of_notMem (show dist x o ∉ Ici R from hR),mul_zero,abs_zero]
      positivity

variable [ProperSpace X] [TopologicalSpace.SeparableSpace X]

lemma identified_heat_tail_bound
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {r R c β t : ℝ} (hc : 0 ≤ c) (hcβ : c ≤ β)
    (hd : MemLp (fun x => Real.exp (-c*dist x o)) 2 m)
    (hsupp : ∀ᵐ x ∂m,r ≤ dist x o → u x = 0) (ht : 0 ≤ t) :
    |∫ x,cheegerHeat h t u x*(Ici R).indicator (fun _ : ℝ => (1:ℝ)) (dist x o) ∂m| ≤
      ‖u‖*‖hd.toLp (fun x => Real.exp (-c*dist x o))‖*
        Real.exp (β^2*t-β*(R-r)+c*R) := by
  have hβ := hc.trans hcβ
  have hV : LipschitzWith ‖β‖₊ (fun x => β*dist x o) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |β*dist x o-β*dist y o| ≤ |β| *dist x y
    rw [← mul_sub,abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_dist_sub_le x y o) (abs_nonneg β)
  have hu := memLp_exp_dist_of_support u hβ o hsupp
  have hw := (identified_cheegerHeat_weighted hID hpar hfin o h u hV hu ht).1
  have hη := tail_exp_weight o hcβ hd (R := R)
  have H := integral_mul_le_weighted hw hη
  change |∫ x,cheegerHeat h t u x*(Ici R).indicator (fun _ : ℝ => (1:ℝ)) (dist x o) ∂m| ≤ _ at H
  have HU := (identified_cheegerHeat_weighted_norm hID hpar hfin o h u hV hu ht).trans
    (mul_le_mul_of_nonneg_right (supported_exp_weight_norm u hβ o hsupp) (Real.exp_pos _).le)
  have HD := tail_exp_weight_norm o hcβ hd (R := R)
  refine H.trans ((mul_le_mul HU HD (norm_nonneg _) (by positivity)).trans_eq ?_)
  simp only [coe_nnnorm,Real.norm_eq_abs,sq_abs]
  rw [show Real.exp (β*r)*‖u‖*Real.exp (β^2*t)*
      (Real.exp (-(β-c)*R)*‖hd.toLp (fun x => Real.exp (-c*dist x o))‖) =
      ‖u‖*‖hd.toLp (fun x => Real.exp (-c*dist x o))‖*
        (Real.exp (β*r)*Real.exp (β^2*t)*Real.exp (-(β-c)*R)) by ring,
    ← Real.exp_add,← Real.exp_add]
  congr 2
  ring

end WeakHessian

end
end

end OAI
