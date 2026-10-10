import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.CostMetric

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile61
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

lemma quadraticWassersteinSq_reweight_bound (μ ν : ProbabilityMeasure X) (ρ : Measure X)
    [IsFiniteMeasure ρ] {a : ℝ≥0∞} (ha : a ≠ ∞)
    (hdec : (μ:Measure X) = a • (ν:Measure X)+ρ) (o : X)
    (hρ : Integrable (fun x => dist x o^2) ρ)
    (hν : Integrable (fun x => dist x o^2) (ν:Measure X)) :
    quadraticWassersteinSq (μ:Measure X) (ν:Measure X) ≤
      2*((∫ x,dist x o^2 ∂ρ)+(ρ univ).toReal*(∫ x,dist x o^2 ∂(ν:Measure X))) := by
  let d : X → X×X := fun x => (x,x)
  have hd : Measurable d := measurable_id.prodMk measurable_id
  let q : Measure (X×X) := (a • (ν:Measure X)).map d+ρ.prod (ν:Measure X)
  have hmass : a+ρ univ = 1 := by
    have H := congrArg (fun μ : Measure X => μ univ) hdec
    simpa only [Measure.add_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one] using H.symm
  have hc : IsCoupling q μ ν := by
    constructor
    · dsimp [q]
      rw [Measure.map_add _ _ measurable_fst,Measure.map_map measurable_fst hd]
      simpa only [d,Function.comp_def,Measure.map_id',Measure.map_fst_prod,measure_univ,one_smul] using hdec.symm
    · dsimp [q]
      rw [Measure.map_add _ _ measurable_snd,Measure.map_map measurable_snd hd]
      simp only [d,Function.comp_def,Measure.map_id',Measure.map_snd_prod,← add_smul,hmass,one_smul]
  have hdiag : Integrable (fun p : X×X => dist p.1 p.2^2) ((a • (ν:Measure X)).map d) := by
    apply (integrable_map_measure ((measurable_fst.dist measurable_snd).pow_const 2).aestronglyMeasurable hd.aemeasurable).mpr
    apply Integrable.smul_measure ?_ ha
    simp [Function.comp_def,d]
  have hbound : Integrable (fun p : X×X => 2*(dist p.1 o^2+dist p.2 o^2)) (ρ.prod (ν:Measure X)) :=
    ((hρ.comp_fst (ν:Measure X)).add (hν.comp_snd ρ)).const_mul 2
  have hle (p : X×X) : dist p.1 p.2^2 ≤ 2*(dist p.1 o^2+dist p.2 o^2) := by
    have H := dist_triangle p.1 o p.2
    rw [dist_comm o p.2] at H
    nlinarith [dist_nonneg (x := p.1) (y := p.2),sq_nonneg (dist p.1 o-dist p.2 o)]
  have hprod : Integrable (fun p : X×X => dist p.1 p.2^2) (ρ.prod (ν:Measure X)) :=
    hbound.mono' ((measurable_fst.dist measurable_snd).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (dist p.1 p.2))] using hle p)
  have hqi : Integrable (fun p : X×X => dist p.1 p.2^2) q := hdiag.add_measure hprod
  have hqt := cost_ne_top_iff_integrable_sq.mpr hqi
  apply (quadraticWassersteinSq_le_cost hc hqt).trans
  rw [quadraticTransportCost_eq_integral hqt,ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  change (∫ p,dist p.1 p.2^2 ∂((a • (ν:Measure X)).map d+ρ.prod (ν:Measure X))) ≤ _
  rw [integral_add_measure hdiag hprod,integral_map hd.aemeasurable ((measurable_fst.dist measurable_snd).pow_const 2).aestronglyMeasurable]
  simp only [d,dist_self,zero_pow (by norm_num : (2:ℕ) ≠ 0),integral_zero,zero_add]
  apply (integral_mono hprod hbound hle).trans_eq
  rw [integral_const_mul,integral_add (hρ.comp_fst (ν:Measure X)) (hν.comp_snd ρ)]
  congr 1
  have h1 : (∫ p : X×X,dist p.1 o^2 ∂ρ.prod (ν:Measure X)) = ∫ x,dist x o^2 ∂ρ := by
    simpa using (integral_prod_mul (fun x => dist x o^2) (fun _ : X => (1:ℝ)) (μ := ρ) (ν := (ν:Measure X)))
  have h2 : (∫ p : X×X,dist p.2 o^2 ∂ρ.prod (ν:Measure X)) = (ρ univ).toReal*(∫ x,dist x o^2 ∂(ν:Measure X)) := by
    simpa [measureReal_def] using (integral_prod_mul (fun _ : X => (1:ℝ)) (fun x => dist x o^2) (μ := ρ) (ν := (ν:Measure X)))
  rw [h1,h2]

lemma quadraticWassersteinSq_reweight_tendsto {ι : Type*} {l : Filter ι}
    (μ : ProbabilityMeasure X) (ν : ι → ProbabilityMeasure X) (ρ : ι → Measure X)
    [∀ i, IsFiniteMeasure (ρ i)] (a : ι → ℝ≥0∞) (hat : ∀ i,a i ≠ ∞)
    (hdec : ∀ i,(μ:Measure X) = a i • (ν i:Measure X)+ρ i) (o : X)
    (hμ : Integrable (fun x => dist x o^2) (μ:Measure X))
    (hν : ∀ i,Integrable (fun x => dist x o^2) (ν i:Measure X))
    (ha : Tendsto (fun i => (a i).toReal) l (𝓝 1))
    (hM : Tendsto (fun i => ∫ x,dist x o^2 ∂(ν i:Measure X)) l (𝓝 (∫ x,dist x o^2 ∂(μ:Measure X)))) :
    Tendsto (fun i => quadraticWassersteinSq (μ:Measure X) (ν i:Measure X)) l (𝓝 0) := by
  have hρle (i) : ρ i ≤ (μ:Measure X) := by
    rw [hdec i]
    exact Measure.le_add_left le_rfl
  have hρ (i) : Integrable (fun x => dist x o^2) (ρ i) := hμ.mono_measure (hρle i)
  have hmass (i) : (a i).toReal+(ρ i univ).toReal = 1 := by
    have H := congrArg (fun μ : Measure X => μ univ) (hdec i)
    have H' : a i+ρ i univ = 1 := by
      simpa only [Measure.add_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one] using H.symm
    have H'' := congrArg ENNReal.toReal H'
    simpa only [ENNReal.toReal_add (hat i) (measure_ne_top _ _),ENNReal.toReal_one] using H''
  have hmoment (i) : (∫ x,dist x o^2 ∂(μ:Measure X)) =
      (a i).toReal*(∫ x,dist x o^2 ∂(ν i:Measure X))+(∫ x,dist x o^2 ∂ρ i) := by
    conv_lhs => rw [hdec i]
    rw [integral_add_measure ((hν i).smul_measure (hat i)) (hρ i),integral_smul_measure,smul_eq_mul]
  have hR : Tendsto (fun i => (ρ i univ).toReal) l (𝓝 0) := by
    have H := (show Tendsto (fun _ : ι => (1:ℝ)) l (𝓝 1) from tendsto_const_nhds).sub ha
    simp only [sub_self] at H
    exact H.congr (fun i => by linarith [hmass i])
  have hRM : Tendsto (fun i => ∫ x,dist x o^2 ∂ρ i) l (𝓝 0) := by
    have H := (show Tendsto (fun _ : ι => ∫ x,dist x o^2 ∂(μ:Measure X)) l (𝓝 (∫ x,dist x o^2 ∂(μ:Measure X))) from tendsto_const_nhds).sub (ha.mul hM)
    simp only [one_mul,sub_self] at H
    exact H.congr (fun i => by linarith [hmoment i])
  have hB := (hRM.add (hR.mul hM)).const_mul 2
  simp only [zero_mul,zero_add,mul_zero] at hB
  apply squeeze_zero (fun i => ENNReal.toReal_nonneg) (fun i => ?_) hB
  exact quadraticWassersteinSq_reweight_bound μ (ν i) (ρ i) (hat i) (hdec i) o (hρ i) (hν i)

lemma quadraticWassersteinSq_tendsto_of_cost_zero {ι : Type*} {l : Filter ι}
    (μ ν : ProbabilityMeasure X) (νs : ι → ProbabilityMeasure X) (o : X)
    (hμ : Integrable (fun x => dist x o^2) (μ:Measure X))
    (hν : Integrable (fun x => dist x o^2) (ν:Measure X))
    (hνs : ∀ i,Integrable (fun x => dist x o^2) (νs i:Measure X))
    (hT : Tendsto (fun i => quadraticWassersteinSq (ν:Measure X) (νs i:Measure X)) l (𝓝 0)) :
    Tendsto (fun i => quadraticWassersteinSq (μ:Measure X) (νs i:Measure X)) l
      (𝓝 (quadraticWassersteinSq (μ:Measure X) (ν:Measure X))) := by
  have hS : Tendsto (fun i => Real.sqrt (quadraticWassersteinSq (ν:Measure X) (νs i:Measure X))) l (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hT.sqrt
  have hSQ : Tendsto (fun i => Real.sqrt (quadraticWassersteinSq (μ:Measure X) (νs i:Measure X))) l
      (𝓝 (Real.sqrt (quadraticWassersteinSq (μ:Measure X) (ν:Measure X)))) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hS.eventually_lt_const hε] with i hi
    rw [Real.dist_eq]
    apply lt_of_le_of_lt (abs_le.mpr ⟨?_,?_⟩) hi
    · have H := quadraticWassersteinSq_triangle μ (νs i) ν o hμ (hνs i) hν
      rw [quadraticWassersteinSq_comm (νs i:Measure X) (ν:Measure X)] at H
      linarith
    · have H := quadraticWassersteinSq_triangle μ ν (νs i) o hμ hν (hνs i)
      linarith
  have H := hSQ.pow 2
  have hn (p q : Measure X) : 0 ≤ quadraticWassersteinSq p q := ENNReal.toReal_nonneg
  simpa only [Real.sq_sqrt (hn _ _)] using H
end WeakHessian

end
end InlinedFile61

end OAI
