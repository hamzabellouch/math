import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityLabelArray

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction

theorem cavity_joint_array_log_limit (n d : ℕ) (M : ℕ→ℕ) (f : Jet3) (v : ℕ→ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (K : ℝ) (hK : ∀ m,M m/(m+1:ℕ)*‖f.d1‖^2≤K) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray (BulkPairRange K))}
    (hbulk : Tendsto (fun j=>bulkMarkedArrayLaw (s j) (M (s j)) f (v (s j)) K (hK (s j))) atTop (𝓝 ν))
    (k : ℕ→ℕ) (p : (j : ℕ)→Fin (k j+1)→BulkPairRange K)
    (D : ℕ→BulkPairRange K) (z : (j : ℕ)→Fin (k j)→ℝ)
    (hp0 : ∀ j i,0≤cavityPairProfile n d (p j) 0 i)
    (hpm : ∀ j i,Monotone (fun l=>cavityPairProfile n d (p j) l i))
    (hpD : ∀ j i,cavityPairProfile n d (p j) (Fin.last (k j)) i≤cavityPairDiagonal n d (D j) i)
    (hrpc : Tendsto (fun j=>cavityLabelMarkedLaw (p j) (D j) (z j)) atTop (𝓝 ν)) :
    Tendsto (fun j=>cavityBulkLog n d (s j) (M (s j)) f (v (s j)) Λ hΛ-
      ∫ x,Real.log x.val ∂(cavityLabelPartitionLaw n d (k j) f.f Λ hΛ
        (fun i=>Real.sqrt (cavityPairDiagonal n d (D j) i-cavityPairProfile n d (p j) (Fin.last (k j)) i))
        (cavityPairProfile n d (p j)) (z j) : Measure (CavityPartitionRange d f.f Λ))) atTop (𝓝 0) := by
  obtain ⟨η,_hη,hm,hlog⟩:=cavityBulkLog_tendsto n d M f v Λ hΛ K hK s hbulk
  let ρ : ℕ→ProbabilityMeasure (CavityPartitionRange d f.f Λ):=fun j=>
    cavityLabelPartitionLaw n d (k j) f.f Λ hΛ
      (fun i=>Real.sqrt (cavityPairDiagonal n d (D j) i-cavityPairProfile n d (p j) (Fin.last (k j)) i))
      (cavityPairProfile n d (p j)) (z j)
  have hr : Tendsto ρ atTop (𝓝 η) := by
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro F
    apply integral_continuous_tendsto_of_moments (fun j=>(ρ j : Measure (CavityPartitionRange d f.f Λ)))
      (η : Measure (CavityPartitionRange d f.f Λ)) (fun r=>?_) F.toContinuousMap
    rw [hm r]
    have ht:=cavityArrayKernel_tendsto n d r f.f Λ hΛ K hrpc
    have he j : (∫ x,x.val^r ∂(ρ j : Measure (CavityPartitionRange d f.f Λ)))=
        ∫ Q,cavityArrayKernel n d r f.f Λ hΛ K Q ∂cavityLabelMarkedLaw (p j) (D j) (z j) :=
      cavityLabelMarkedLaw_cavity_moment n d (p j) (D j) (z j) (hp0 j) (hpm j) (hpD j) f.f Λ hΛ r
    simp_rw [he]
    exact ht
  have hl := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (cavityPartitionLogTest d f.f Λ)).continuousAt.tendsto.comp hr
  have hd:=hlog.sub hl
  simpa only [Function.comp_def,cavityPartitionLogTest,BoundedContinuousFunction.mkOfCompact_apply,
    ContinuousMap.coe_mk,sub_self,ρ] using hd

theorem cavity_joint_array_recursion_limit (n d : ℕ) (M : ℕ→ℕ) (f : Jet3) (v : ℕ→ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (K : ℝ) (hK : ∀ m,M m/(m+1:ℕ)*‖f.d1‖^2≤K) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray (BulkPairRange K))}
    (hbulk : Tendsto (fun j=>bulkMarkedArrayLaw (s j) (M (s j)) f (v (s j)) K (hK (s j))) atTop (𝓝 ν))
    (k : ℕ→ℕ) (p : (j : ℕ)→Fin (k j+1)→BulkPairRange K)
    (D : ℕ→BulkPairRange K) (z : (j : ℕ)→Fin (k j)→ℝ)
    (hp0 : ∀ j i,0≤cavityPairProfile n d (p j) 0 i)
    (hpm : ∀ j i,Monotone (fun l=>cavityPairProfile n d (p j) l i))
    (hpD : ∀ j i,cavityPairProfile n d (p j) (Fin.last (k j)) i≤cavityPairDiagonal n d (D j) i)
    (hz : ∀ j,StrictMono (z j)) (hz0 : ∀ j i,0<z j i) (hz1 : ∀ j i,z j i<1)
    (hrpc : Tendsto (fun j=>cavityLabelMarkedLaw (p j) (D j) (z j)) atTop (𝓝 ν)) :
    Tendsto (fun j=>cavityBulkLog n d (s j) (M (s j)) f (v (s j)) Λ hΛ-
      ∫ y,finiteCascadeLogRecursion (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))
        (gaussianLinearMarkStep (fun l=>diagonalMark (profileGaussianStep (cavityPairProfile n d (p j)) l))) (k j) (z j)
        (fun t=>Real.log (cavityDiagonalAverage
          (fun i=>Real.sqrt (cavityPairDiagonal n d (D j) i-cavityPairProfile n d (p j) (Fin.last (k j)) i))
          (cavitySingleTest n d f.f Λ hΛ) (t 0)))
        (fun _=>diagonalMark (profileGaussianRoot (cavityPairProfile n d (p j))) y)
        ∂stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d))) atTop (𝓝 0) := by
  have ht:=cavity_joint_array_log_limit n d M f v Λ hΛ K hK s hbulk k p D z hp0 hpm hpD hrpc
  simpa only [cavityLabelPartitionLaw_log_recursion n d _ f.f Λ hΛ _ _ _ (hz _) (hz0 _) (hz1 _)] using ht

lemma cavity_expected_cap_ae {S G : Type*} [MeasurableSpace S] [MeasurableSpace G]
    (μ : Measure S) (P : Measure G) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (W F : G×S→ℝ) (hW : Measurable W) (hF : Measurable F) {C Λ K : ℝ}
    (hWC : ∀ p,|W p|≤C) (hF1 : ∀ p,1≤F p) (hΛ : 1≤Λ)
    (hFg : ∀ x,MemLp (fun g=>F (g,x)) 2 P)
    (h2 : ∀ x,(∫ g,F (g,x)^2 ∂P)≤K) :
    let D:=fun g=>Real.log (∫ x,Real.exp (W (g,x))*F (g,x) ∂μ)-
      Real.log (∫ x,Real.exp (W (g,x))*min (F (g,x)) Λ ∂μ)
    Integrable D P ∧ 0≤∫ g,D g ∂P ∧
      (∫ g,D g ∂P)≤Real.exp (2*C)/Λ*K := by
  let Q : S×G→ℝ := fun p=>F (p.2,p.1)^2
  have hQ : Measurable Q := (hF.comp measurable_swap).pow_const 2
  have hi : Integrable Q (μ.prod P) := by
    apply (integrable_prod_iff hQ.aestronglyMeasurable).mpr
    constructor
    · exact ae_of_all _ fun x=>(memLp_two_iff_integrable_sq (hFg x).aestronglyMeasurable).mp (hFg x)
    · apply Integrable.of_bound (hQ.norm.stronglyMeasurable.integral_prod_right).aestronglyMeasurable K
      filter_upwards [] with x
      have he : (∫ g,‖Q (x,g)‖ ∂P)=(∫ g,F (g,x)^2 ∂P) := by
        simp only [Q,Real.norm_eq_abs,abs_sq]
      rw [he,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun g=>sq_nonneg _)]
      exact h2 x
  have hS : Integrable (fun g=>∫ x,F (g,x)^2 ∂μ) P := hi.integral_prod_right
  have hB : (∫ g,∫ x,F (g,x)^2 ∂μ ∂P)≤K := by
    rw [←integral_integral_swap hi]
    calc
      _≤∫ _ : S,K ∂μ := integral_mono hi.integral_prod_left (integrable_const _) h2
      _=K := by simp
  let D:=fun g=>Real.log (∫ x,Real.exp (W (g,x))*F (g,x) ∂μ)-
    Real.log (∫ x,Real.exp (W (g,x))*min (F (g,x)) Λ ∂μ)
  have hD : Measurable D := by
    exact ((hW.exp.mul hF).stronglyMeasurable.integral_prod_right.measurable.log).sub
      ((hW.exp.mul (hF.min measurable_const)).stronglyMeasurable.integral_prod_right.measurable.log)
  have hFx : ∀ᵐ g ∂P,MemLp (fun x=>F (g,x)) 2 μ := by
    filter_upwards [hi.prod_left_ae] with g hg
    apply (memLp_two_iff_integrable_sq
      ((hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)).mpr
    exact hg
  have hp : ∀ᵐ g ∂P,0≤D g ∧ D g≤Real.exp (2*C)/Λ*(∫ x,F (g,x)^2 ∂μ) := by
    filter_upwards [hFx] with g hg
    exact cavity_capped_log_bound μ (hW.comp (measurable_const.prodMk measurable_id))
      (fun x=>hWC (g,x)) hg (fun x=>hF1 (g,x)) hΛ
  have hc : 0≤Real.exp (2*C)/Λ := div_nonneg (Real.exp_pos _).le ((by norm_num : (0:ℝ)≤1).trans hΛ)
  have hDi : Integrable D P := by
    apply (hS.const_mul (Real.exp (2*C)/Λ)).mono' hD.aestronglyMeasurable
    filter_upwards [hp] with g hg
    simpa only [Real.norm_eq_abs,abs_of_nonneg hg.1] using hg.2
  refine ⟨hDi,integral_nonneg_of_ae (hp.mono fun _point hg=>hg.1),?_⟩
  calc
    _≤∫ g,Real.exp (2*C)/Λ*(∫ x,F (g,x)^2 ∂μ) ∂P :=
      integral_mono_ae hDi (hS.const_mul _) (hp.mono fun _point hg=>hg.2)
    _=Real.exp (2*C)/Λ*(∫ g,∫ x,F (g,x)^2 ∂μ ∂P) := integral_const_mul _ _
    _≤_ := mul_le_mul_of_nonneg_left hB hc

lemma cavity_expected_cap_integrated {S G : Type*} [MeasurableSpace S] [MeasurableSpace G]
    (μ : Measure S) (P : Measure G) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (W F : G×S→ℝ) (hW : Measurable W) (hF : Measurable F) {C Λ K : ℝ}
    (hWC : ∀ p,|W p|≤C) (hF1 : ∀ p,1≤F p) (hΛ : 1≤Λ)
    (hF2 : Integrable (fun p : G×S=>F p^2) (P.prod μ))
    (h2 : (∫ g,∫ x,F (g,x)^2 ∂μ ∂P)≤K) :
    let D:=fun g=>Real.log (∫ x,Real.exp (W (g,x))*F (g,x) ∂μ)-
      Real.log (∫ x,Real.exp (W (g,x))*min (F (g,x)) Λ ∂μ)
    Integrable D P ∧ 0≤∫ g,D g ∂P ∧
      (∫ g,D g ∂P)≤Real.exp (2*C)/Λ*K := by
  have hS : Integrable (fun g=>∫ x,F (g,x)^2 ∂μ) P := hF2.integral_prod_left
  let D:=fun g=>Real.log (∫ x,Real.exp (W (g,x))*F (g,x) ∂μ)-
    Real.log (∫ x,Real.exp (W (g,x))*min (F (g,x)) Λ ∂μ)
  have hD : Measurable D := by
    exact ((hW.exp.mul hF).stronglyMeasurable.integral_prod_right.measurable.log).sub
      ((hW.exp.mul (hF.min measurable_const)).stronglyMeasurable.integral_prod_right.measurable.log)
  have hFx : ∀ᵐ g ∂P,MemLp (fun x=>F (g,x)) 2 μ := by
    filter_upwards [hF2.prod_right_ae] with g hg
    exact (memLp_two_iff_integrable_sq
      ((hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)).mpr hg
  have hp : ∀ᵐ g ∂P,0≤D g ∧ D g≤Real.exp (2*C)/Λ*(∫ x,F (g,x)^2 ∂μ) := by
    filter_upwards [hFx] with g hg
    exact cavity_capped_log_bound μ (hW.comp (measurable_const.prodMk measurable_id))
      (fun x=>hWC (g,x)) hg (fun x=>hF1 (g,x)) hΛ
  have hc : 0≤Real.exp (2*C)/Λ := div_nonneg (Real.exp_pos _).le ((by norm_num : (0:ℝ)≤1).trans hΛ)
  have hDi : Integrable D P := by
    apply (hS.const_mul (Real.exp (2*C)/Λ)).mono' hD.aestronglyMeasurable
    filter_upwards [hp] with g hg
    simpa only [Real.norm_eq_abs,abs_of_nonneg hg.1] using hg.2
  refine ⟨hDi,integral_nonneg_of_ae (hp.mono fun _point hg=>hg.1),?_⟩
  calc
    _≤∫ g,Real.exp (2*C)/Λ*(∫ x,F (g,x)^2 ∂μ) ∂P :=
      integral_mono_ae hDi (hS.const_mul _) (hp.mono fun _point hg=>hg.2)
    _=Real.exp (2*C)/Λ*(∫ g,∫ x,F (g,x)^2 ∂μ ∂P) := integral_const_mul _ _
    _≤_ := mul_le_mul_of_nonneg_left h2 hc

end SphericalPerceptronFreeEnergy
end

end OAI
