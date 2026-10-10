import Mathlib
import OAI.Probability.LogConcave.Dynamics.ProbabilityFlowIntegral
import OAI.Probability.LogConcave.Sampling.MeasureSmoothLipschitz
import OAI.Probability.LogConcave.Sampling.ClosedFieldMean

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open Set Function MeasureTheory Filter ProbabilityTheory
open scoped Topology

def fullProbabilityFlow {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (t : ℝ) (z : Point d) : Point d :=
  GlobalODE.flow (a:=0) (b:=1) (fun t _ => fullProbabilityVelocity_lipschitz hF x hr hl t)
    (fullProbabilityVelocity_continuous hF x hr hl) ⟨0,le_rfl,by norm_num⟩ z t

lemma fullProbabilityFlow_time_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (z : Point d) : Continuous (fun t => fullProbabilityFlow hF x hr hl t z) :=
  GlobalODE.flow_continuous _ _ _ _

lemma fullProbabilityFlow_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r t : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (ht : t∈Icc 0 1) :
    LipschitzWith ⟨Real.exp (((Real.pi^2/2)*(lam:ℝ)*r^2)*|t|),(Real.exp_pos _).le⟩
      (fullProbabilityFlow hF x hr hl t) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have hh := GlobalODE.trajectory_dist (a:=0) (b:=1)
    (fun t _ => fullProbabilityVelocity_lipschitz hF x hr hl t)
    (fullProbabilityFlow_time_continuous hF x hr hl u).continuousOn
    (GlobalODE.flow_deriv (a:=0) (b:=1)
      (fun t _ => fullProbabilityVelocity_lipschitz hF x hr hl t)
      (fullProbabilityVelocity_continuous hF x hr hl) ⟨0,le_rfl,by norm_num⟩ u)
    (fullProbabilityFlow_time_continuous hF x hr hl v).continuousOn
    (GlobalODE.flow_deriv (a:=0) (b:=1)
      (fun t _ => fullProbabilityVelocity_lipschitz hF x hr hl t)
      (fullProbabilityVelocity_continuous hF x hr hl) ⟨0,le_rfl,by norm_num⟩ v)
    ⟨0,le_rfl,by norm_num⟩ ⟨t,ht⟩
  have hu0 : fullProbabilityFlow hF x hr hl 0 u=u := GlobalODE.flow_initial _ _ _ _
  have hv0 : fullProbabilityFlow hF x hr hl 0 v=v := GlobalODE.flow_initial _ _ _ _
  change dist (fullProbabilityFlow hF x hr hl t u) (fullProbabilityFlow hF x hr hl t v) ≤
    dist (fullProbabilityFlow hF x hr hl 0 u) (fullProbabilityFlow hF x hr hl 0 v)*_ at hh
  rw [hu0,hv0,sub_zero,mul_comm] at hh
  exact hh

lemma fullProbabilityFlow_eq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    fullProbabilityFlow hF x hr hl T=probabilityFlow hF x hr hl hT0 hT1 := by
  funext z
  let α := fun t => fullProbabilityFlow hF x hr hl t z
  let hL := fun t (_ : t∈Icc 0 T) => clampedProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 t
  let hc := clampedProbabilityVelocity_continuous hF x hr hl hT0 hT1
  let β := GlobalODE.flow hL hc ⟨0,le_rfl,hT0⟩ z
  have hsub : Icc (0:ℝ) T ⊆ Icc 0 1 := Icc_subset_Icc_right hT1.le
  have hdα : ∀ t∈Icc (0:ℝ) T, HasDerivWithinAt α
      (clampedProbabilityVelocity F x r T hT0 t (α t)) (Icc 0 T) t := by
    intro t ht
    have hh := GlobalODE.flow_deriv (a:=0) (b:=1)
      (fun t _ => fullProbabilityVelocity_lipschitz hF x hr hl t)
      (fullProbabilityVelocity_continuous hF x hr hl) ⟨0,le_rfl,by norm_num⟩ z t (hsub ht)
    have he : fullProbabilityVelocity F x r t=clampedProbabilityVelocity F x r T hT0 t := by
      funext y
      rw [fullProbabilityVelocity_eq F x r ht.1 (ht.2.trans_lt hT1),clampedProbabilityVelocity_eq F x r T hT0 ht]
    rw [he] at hh
    exact hh.mono hsub
  have hh := GlobalODE.trajectory_dist hL
    (fullProbabilityFlow_time_continuous hF x hr hl z).continuousOn hdα
    (GlobalODE.flow_continuous hL hc ⟨0,le_rfl,hT0⟩ z).continuousOn
    (GlobalODE.flow_deriv hL hc ⟨0,le_rfl,hT0⟩ z)
    ⟨0,le_rfl,hT0⟩ ⟨T,hT0,le_rfl⟩
  have ha0 : α 0=z := GlobalODE.flow_initial _ _ _ _
  have hb0 : β 0=z := GlobalODE.flow_initial _ _ _ _
  change dist (α T) (β T)≤dist (α 0) (β 0)*_ at hh
  rw [ha0,hb0,dist_self,zero_mul,dist_le_zero] at hh
  exact hh

lemma fullProbabilityFlow_integral {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1)
    {φ : Point d → ℝ} (hφ : Differentiable ℝ φ) {L : ℝ≥0} (hφL : LipschitzWith L φ)
    {B : ℝ} (hB : ∀ z,|φ z|≤B) :
    (∫ z,φ (fullProbabilityFlow hF x hr hl T z) ∂stdGaussian (Point d))=
      ∫ p,φ (interpolationPath T p) ∂(gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)) := by
  rw [fullProbabilityFlow_eq hF x hr hl hT0.le hT1]
  have hh := probabilityFlow_integral hF x hr hl hT0 hT1 hφ hφL hB
  change (∫ y, φ y ∂Measure.map (interpolationPath T)
    ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)))) = _ at hh
  rw [integral_map (interpolationPath_measurable T).aemeasurable
    hφ.continuous.aestronglyMeasurable] at hh
  exact hh.symm

lemma fullProbabilityFlow_endpoint_integral {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2)
    {φ : Point d → ℝ} (hφ : Differentiable ℝ φ) {L : ℝ≥0} (hφL : LipschitzWith L φ)
    {B : ℝ} (hB : ∀ z,|φ z|≤B) :
    (∫ z,φ (fullProbabilityFlow hF x hr hl 1 z) ∂stdGaussian (Point d))=
      ∫ z,φ z ∂gibbs (primitivePotential F x r) := by
  let μ := gibbs (primitivePotential F x r)
  let ν := stdGaussian (Point d)
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr (by linarith)))
  let t : ℕ → ℝ := fun n => 1-(1/2:ℝ)^(n+1)
  have ht0 (n : ℕ) : 0<t n := by
    have hh : (1/2:ℝ)^(n+1)<1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    dsimp [t]; linarith
  have ht1 (n : ℕ) : t n<1 := by
    have hh : 0 < (1/2:ℝ)^(n+1) := by positivity
    dsimp [t]; linarith
  have ht : Tendsto t atTop (𝓝 1) := by
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(1/2:ℝ)) (by norm_num)).mul_const (1/2:ℝ)
    simpa only [zero_mul,sub_zero,←pow_succ] using (tendsto_const_nhds (x:=(1:ℝ))).sub hh
  have hleft : Tendsto (fun n => ∫ z,φ (fullProbabilityFlow hF x hr hl (t n) z) ∂ν)
      atTop (𝓝 (∫ z,φ (fullProbabilityFlow hF x hr hl 1 z) ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => B)
      (fun n => (hφ.continuous.comp (fullProbabilityFlow_lipschitz hF x hr hl ⟨(ht0 n).le,(ht1 n).le⟩).continuous).aestronglyMeasurable)
      (integrable_const B)
    · intro n
      exact Filter.Eventually.of_forall (fun z => by simpa only [Function.comp_apply,Real.norm_eq_abs] using hB (fullProbabilityFlow hF x hr hl (t n) z))
    · exact Filter.Eventually.of_forall (fun z => (hφ.continuous.comp
        (fullProbabilityFlow_time_continuous hF x hr hl z)).continuousAt.tendsto.comp ht)
  have hright : Tendsto (fun n => ∫ p,φ (interpolationPath (t n) p) ∂μ.prod ν)
      atTop (𝓝 (∫ p,φ p.1 ∂μ.prod ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => B)
      (fun n => (hφ.continuous.comp (by unfold interpolationPath; fun_prop)).aestronglyMeasurable)
      (integrable_const B)
    · intro n
      exact Filter.Eventually.of_forall (fun p => by simpa only [Function.comp_apply,Real.norm_eq_abs] using hB (interpolationPath (t n) p))
    · filter_upwards [] with p
      have hc : Continuous (fun t : ℝ => φ (interpolationPath t p)) := by
        apply hφ.continuous.comp
        unfold interpolationPath
        fun_prop
      simpa [Function.comp_def,interpolationPath] using hc.continuousAt.tendsto.comp ht
  have he : (fun n => ∫ p,φ (interpolationPath (t n) p) ∂μ.prod ν)=
      (fun n => ∫ z,φ (fullProbabilityFlow hF x hr hl (t n) z) ∂ν) := by
    funext n
    exact (fullProbabilityFlow_integral hF x hr hl (ht0 n) (ht1 n) hφ hφL hB).symm
  rw [he] at hright
  have hh := tendsto_nhds_unique hleft hright
  simpa only [integral_fun_fst,probReal_univ,one_smul] using hh

theorem fullProbabilityFlow_pushforward {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) :
    (stdGaussian (Point d)).map (fullProbabilityFlow hF x hr hl 1)=gibbs (primitivePotential F x r) := by
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr (by linarith)))
  have hc := (fullProbabilityFlow_lipschitz hF x hr hl (t:=1) ⟨by norm_num,le_rfl⟩).continuous
  apply measure_eq_of_smooth_lipschitz
  intro φ hφ ⟨L,hL⟩ ⟨B,hB⟩
  rw [integral_map hc.measurable.aemeasurable hφ.continuous.aestronglyMeasurable]
  exact fullProbabilityFlow_endpoint_integral hF x hr hl (hφ.differentiable (by norm_num)) hL hB
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
