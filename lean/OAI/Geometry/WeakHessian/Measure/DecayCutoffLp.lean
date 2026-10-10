import Mathlib
import OAI.Geometry.WeakHessian.Calculus.NormLpSqIntegral
import OAI.Geometry.WeakHessian.Measure.RadialCutoffLp

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma integral_mul_le_weighted {V f η : X → ℝ}
    (hf : MemLp (fun x => f x*Real.exp (V x)) 2 m)
    (hη : MemLp (fun x => Real.exp (-V x)*η x) 2 m) :
    ‖∫ x, f x*η x ∂m‖ ≤
      ‖hf.toLp (fun x => f x*Real.exp (V x))‖*
      ‖hη.toLp (fun x => Real.exp (-V x)*η x)‖ := by
  let U := hf.toLp (fun x => f x*Real.exp (V x))
  let W := hη.toLp (fun x => Real.exp (-V x)*η x)
  have he : (∫ x, f x*η x ∂m) = ⟪U,W⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hη.coeFn_toLp] with x hu hw
    dsimp only [U,W]
    rw [hu,hw]
    simp only [RCLike.inner_apply,conj_trivial]
    calc f x*η x = f x*(Real.exp (V x)*Real.exp (-V x))*η x := by
           rw [← Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
         _ = _ := by ring
  rw [he]
  exact norm_inner_le_norm _ _

variable [MetricSpace X] [BorelSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X]

omit [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma memLp_decayCutoff {V : X → ℝ} (hV : MemLp (fun x => Real.exp (-V x)) 2 m)
    (o : X) (n : ℕ) : MemLp (fun x => Real.exp (-V x)*(1-radialCutoff o n x)) 2 m := by
  apply memLp_mul_bounded hV (B := 1) (aestronglyMeasurable_const.sub
    (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable)
  exact ae_of_all _ fun x => by
    change |1-radialCutoff o n x| ≤ (1:ℝ)
    rw [abs_of_nonneg (sub_nonneg.mpr (radialCutoff_le_one o n x))]
    linarith [radialCutoff_nonneg o n x]

noncomputable def decayCutoffLp {V : X → ℝ} (hV : MemLp (fun x => Real.exp (-V x)) 2 m)
    (o : X) (n : ℕ) : Lp ℝ 2 m :=
  (memLp_decayCutoff hV o n).toLp (fun x => Real.exp (-V x)*(1-radialCutoff o n x))

omit [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma decayCutoffLp_norm_tendsto {V : X → ℝ} (hV : MemLp (fun x => Real.exp (-V x)) 2 m)
    (o : X) : Tendsto (fun n => ‖decayCutoffLp hV o n‖) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => ‖decayCutoffLp hV o n‖^2) atTop (𝓝 0) := by
    have H := tendsto_integral_of_dominated_convergence (F := fun n x => (Real.exp (-V x)*(1-radialCutoff o n x))^2) (f := fun _ => (0:ℝ)) (fun x => (Real.exp (-V x))^2)
      (fun n => (memLp_decayCutoff hV o n).aestronglyMeasurable.pow 2) hV.integrable_sq
      (fun n => ae_of_all _ fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),mul_pow]
        apply mul_le_of_le_one_right (sq_nonneg _)
        have h0 := radialCutoff_nonneg o n x
        have h1 := radialCutoff_le_one o n x
        nlinarith [sq_nonneg (radialCutoff o n x)])
      (ae_of_all _ fun x => by
        have H := ((tendsto_const_nhds (x := Real.exp (-V x))).mul ((tendsto_const_nhds (x := (1:ℝ))).sub (radialCutoff_tendsto o x))).pow 2
        simpa only [sub_self,mul_zero,zero_pow (by decide : (2:ℕ) ≠ 0)] using H)
    simpa only [decayCutoffLp,norm_toLp_sq_eq_integral,integral_zero] using H
  have H := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using H

omit [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma integral_cutoff_error_le_weighted {V f : X → ℝ}
    (hf : MemLp (fun x => f x*Real.exp (V x)) 2 m)
    (hV : MemLp (fun x => Real.exp (-V x)) 2 m) (o : X) (n : ℕ) :
    ‖(∫ x,f x ∂m)-(∫ x,f x*radialCutoff o n x ∂m)‖ ≤
      ‖hf.toLp (fun x => f x*Real.exp (V x))‖*‖decayCutoffLp hV o n‖ := by
  have hfi := integrable_of_memLp_mul_exp hf hV
  have hη : Integrable (fun x => f x*radialCutoff o n x) m :=
    hfi.mul_bdd (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable
      (ae_of_all _ fun x => by
        change |radialCutoff o n x| ≤ (1:ℝ)
        rw [abs_of_nonneg (radialCutoff_nonneg o n x)]
        exact radialCutoff_le_one o n x)
  have he : (∫ x,f x ∂m)-(∫ x,f x*radialCutoff o n x ∂m) =
      ∫ x,f x*(1-radialCutoff o n x) ∂m := by
    rw [← integral_sub hfi hη]
    congr 1; funext x; simp only [mul_sub,mul_one]
  rw [he]
  exact integral_mul_le_weighted hf (memLp_decayCutoff hV o n)

lemma integral_tendsto_of_weighted_bound {V : X → ℝ}
    (hV : MemLp (fun x => Real.exp (-V x)) 2 m)
    (hfinite : FiniteOnBoundedSets m) (o : X)
    {fs : ℕ → Lp ℝ 2 m} {f : Lp ℝ 2 m} (hlim : Tendsto fs atTop (𝓝 f))
    (hf : MemLp (fun x => f x*Real.exp (V x)) 2 m)
    (hfs : ∀ n, MemLp (fun x => fs n x*Real.exp (V x)) 2 m)
    {B : ℝ} (hB : ∀ n, ‖(hfs n).toLp (fun x => fs n x*Real.exp (V x))‖ ≤ B) :
    Tendsto (fun n => ∫ x,fs n x ∂m) atTop (𝓝 (∫ x,f x ∂m)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  let D := ‖hf.toLp (fun x => f x*Real.exp (V x))‖
  have htail : Tendsto (fun j => (B+D)*‖decayCutoffLp hV o j‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using (decayCutoffLp_norm_tendsto hV o).const_mul (B+D)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨j,hj⟩ := (htail.eventually_lt_const (half_pos hε)).exists
  have hc : Tendsto (fun n => ∫ x,fs n x*radialCutoff o j x ∂m) atTop
      (𝓝 (∫ x,f x*radialCutoff o j x ∂m)) := by
    simp_rw [integral_radialCutoff_eq_inner hfinite o j]
    exact (innerSL ℝ (radialCutoffLp hfinite o j)).continuous.continuousAt.tendsto.comp hlim
  filter_upwards [(Metric.tendsto_nhds.mp hc) (ε/2) (half_pos hε)] with n hn
  have he1 := (integral_cutoff_error_le_weighted (hfs n) hV o j).trans
    (mul_le_mul_of_nonneg_right (hB n) (norm_nonneg _))
  have he2 := integral_cutoff_error_le_weighted hf hV o j
  have htri := dist_triangle (∫ x,fs n x ∂m) (∫ x,fs n x*radialCutoff o j x ∂m) (∫ x,f x ∂m)
  have htri2 := dist_triangle (∫ x,fs n x*radialCutoff o j x ∂m)
    (∫ x,f x*radialCutoff o j x ∂m) (∫ x,f x ∂m)
  simp only [dist_eq_norm] at htri htri2 hn ⊢
  rw [norm_sub_rev (∫ x,f x*radialCutoff o j x ∂m)] at htri2
  dsimp only [D] at hj
  nlinarith
end WeakHessian

end
end InlinedFile0

end OAI
