import Mathlib
import OAI.Geometry.WeakHessian.Transport.BoundedHopfMapNorm

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile231
noncomputable section
namespace WeakHessianTransport
open WeakHessian Set Filter MeasureTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X]

lemma hopf_diff_of_local_bound (f g : X →ᵇ ℝ) (x : X) {B ε : ℝ}
    (hB : 0 ≤ B) (hf : ∀ y,|f y| ≤ B) (hg : ∀ y,|g y| ≤ B)
    (hfg : ∀ y,dist x y ≤ B+2 → |f y-g y| ≤ ε) :
    |hopfLax f 1 x-hopfLax g 1 x| ≤ ε := by
  obtain ⟨y,hy⟩ := exists_hopf_minimizer f.continuous (fun z => (abs_le.mp (hf z)).1) (by norm_num : (0:ℝ)<1) x
  obtain ⟨z,hz⟩ := exists_hopf_minimizer g.continuous (fun z => (abs_le.mp (hg z)).1) (by norm_num : (0:ℝ)<1) x
  have hdist (q : X →ᵇ ℝ) (hq : ∀ y,|q y| ≤ B) (w : X)
      (hw : hopfObjective q 1 x w = hopfLax q 1 x) : dist x w ≤ B+2 :=
    hopf_minimizer_distance_le (fun z => (abs_le.mp (hq z)).1) (fun z => (abs_le.mp (hq z)).2)
      (by norm_num) (by positivity) (by nlinarith [sq_nonneg B]) hw
  have H₁ := hopfLax_le_objective (fun z => (abs_le.mp (hf z)).1) (by norm_num : (0:ℝ)<1) x z
  have H₂ := hopfLax_le_objective (fun z => (abs_le.mp (hg z)).1) (by norm_num : (0:ℝ)<1) x y
  have ey := abs_le.mp (hfg y (hdist f hf y hy))
  have ez := abs_le.mp (hfg z (hdist g hg z hz))
  dsimp only [hopfObjective] at hy hz H₁ H₂
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma exists_compact_hopf_approx (f : X →ᵇ ℝ) (o : X) (hL : GloballyLipschitz (f:X→ℝ)) :
    ∃ fs : ℕ → X →ᵇ ℝ,
      (∀ n,HasCompactSupport (fs n:X→ℝ) ∧ GloballyLipschitz (fs n:X→ℝ)) ∧
      (∀ n x,|fs n x| ≤ ‖f‖) ∧
      (∀ x,Tendsto (fun n => fs n x) atTop (𝓝 (f x))) ∧
      (∀ x,Tendsto (fun n => boundedHopfMap (fs n) 1 x) atTop (𝓝 (boundedHopfMap f 1 x))) := by
  have hb (x : X) : |f x| ≤ ‖f‖ := by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x
  have hη (n : ℕ) (x : X) : |radialCutoff o n x| ≤ 1 := by
    rw [abs_of_nonneg (radialCutoff_nonneg _ _ _)]
    exact radialCutoff_le_one _ _ _
  have hfb (n : ℕ) (x : X) : ‖f x*radialCutoff o n x‖ ≤ ‖f‖ := by
    rw [Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul (hb x) (hη n x) (abs_nonneg _) (norm_nonneg f)).trans_eq (mul_one _)
  let fs (n : ℕ) : X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => f x*radialCutoff o n x) (f.continuous.mul (radialCutoff_lipschitz o n).continuous) ‖f‖ (hfb n)
  have hfs (n : ℕ) (x : X) : fs n x = f x*radialCutoff o n x := rfl
  have hfsb (n : ℕ) (x : X) : |fs n x| ≤ ‖f‖ := by simpa only [hfs,Real.norm_eq_abs] using hfb n x
  refine ⟨fs,?_,hfsb,?_,?_⟩
  · intro n
    refine ⟨(radialCutoff_compact o n).mul_left,?_⟩
    exact ⟨_, lipschitz_mul_bounded hL.choose_spec (radialCutoff_lipschitz o n) hb (hη n)⟩
  · intro x
    simpa only [hfs,mul_one] using (tendsto_const_nhds.mul (radialCutoff_tendsto o x) :
      Tendsto (fun n => f x*radialCutoff o n x) atTop (𝓝 (f x*1)))
  · intro x
    have he (n : ℕ) (y : X) : |f y-fs n y| ≤ ‖f‖*dist y o/((n:ℝ)+1) := by
      rw [hfs,← mul_one_sub,abs_mul,abs_of_nonneg (sub_nonneg.mpr (radialCutoff_le_one _ _ _))]
      have hηe : 1-radialCutoff o n y ≤ dist y o/((n:ℝ)+1) := by
        have H := le_max_right (0:ℝ) (1-dist y o/((n:ℝ)+1))
        change 1-max 0 (1-dist y o/((n:ℝ)+1)) ≤ _
        linarith
      simpa only [mul_div_assoc] using mul_le_mul (hb y) hηe
        (sub_nonneg.mpr (radialCutoff_le_one _ _ _)) (norm_nonneg f)
    let E (n : ℕ) := ‖f‖*(dist x o+‖f‖+2)/((n:ℝ)+1)
    have hE (n : ℕ) : |hopfLax f 1 x-hopfLax (fs n) 1 x| ≤ E n := by
      apply hopf_diff_of_local_bound f (fs n) x (norm_nonneg f) hb (hfsb n)
      intro y hy
      apply (he n y).trans
      have hd : dist y o ≤ dist x o+‖f‖+2 := by
        have H := dist_triangle y x o
        rw [dist_comm y x] at H
        linarith
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd (norm_nonneg f)) (by positivity)
    have hEt : Tendsto E atTop (𝓝 0) := by
      have H := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (‖f‖*(dist x o+‖f‖+2))
      simpa only [E,mul_one_div,mul_zero] using H
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨n,hn⟩ := (Metric.tendsto_atTop.mp hEt) ε hε
    refine ⟨n,fun b hb' => ?_⟩
    rw [Real.dist_eq,boundedHopfMap_apply_pos (fs b) (by norm_num),boundedHopfMap_apply_pos f (by norm_num),abs_sub_comm]
    apply (hE b).trans_lt
    have H := hn b hb'
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (by dsimp [E]; positivity)] at H
    exact H

variable [MeasurableSpace X] [BorelSpace X] [TopologicalSpace.SeparableSpace X]

lemma exists_proper_coupling_cost_of_compact_hopf_bound (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (o : X) (B : ℝ)
    (hdual : ∀ f : X →ᵇ ℝ, HasCompactSupport (f:X→ℝ) → GloballyLipschitz (f:X→ℝ) →
      (∫ x,boundedHopfMap f 1 x ∂μ)-(∫ x,f x ∂ν) ≤ B/2) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧
      q.map Prod.fst = μ ∧ q.map Prod.snd = ν ∧
      (∫⁻ p, (edist p.1 p.2)^2 ∂q) ≤ ENNReal.ofReal B := by
  apply exists_proper_coupling_cost_of_hopf_bound μ ν B
  intro f hL
  obtain ⟨fs,hfs,hb,hlim,hQlim⟩ := exists_compact_hopf_approx f o hL
  have hnorm (n : ℕ) : ‖fs n‖ ≤ ‖f‖ := by
    apply BoundedContinuousFunction.norm_le (norm_nonneg f) |>.mpr
    intro x
    simpa only [Real.norm_eq_abs] using hb n x
  have hfn : Tendsto (fun n => ∫ x,fs n x ∂ν) atTop (𝓝 (∫ x,f x ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
      (fun n => (fs n).continuous.aestronglyMeasurable) (integrable_const _)
    · intro n
      exact ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb n x
    · exact ae_of_all _ hlim
  have hQn : Tendsto (fun n => ∫ x,boundedHopfMap (fs n) 1 x ∂μ) atTop
      (𝓝 (∫ x,boundedHopfMap f 1 x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
      (fun n => (boundedHopfMap (fs n) 1).continuous.aestronglyMeasurable) (integrable_const _)
    · intro n
      exact ae_of_all _ fun x => ((boundedHopfMap (fs n) 1).norm_coe_le_norm x).trans
        ((boundedHopfMap_norm_le (fs n) 1).trans (hnorm n))
    · exact ae_of_all _ hQlim
  have H := le_of_tendsto (hQn.sub hfn) (Eventually.of_forall fun n => hdual (fs n) (hfs n).1 (hfs n).2)
  simpa only [boundedHopfMap_apply_pos f (by norm_num : (0:ℝ)<1)] using H
end WeakHessianTransport

end
end InlinedFile231

end OAI
