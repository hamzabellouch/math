import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityIncrementLaw
import OAI.Probability.Perceptron.Cavity.CavityBulkUncappedLog

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavity_three_integral {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) (ν : Measure B) (ρ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite ρ] (F : A×B×C→ℝ)
    (hF : Integrable F (μ.prod (ν.prod ρ))) :
    (∫ p,F p ∂μ.prod (ν.prod ρ))=∫ a,∫ b,∫ c,F (a,b,c) ∂ρ ∂ν ∂μ := by
  rw [integral_prod _ hF]
  apply integral_congr_ae
  filter_upwards [hF.prod_right_ae] with a ha
  exact integral_prod _ ha

lemma cavity_three_integral_compare {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) (ν : Measure B) (ρ : Measure C)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (F G : A×B×C→ℝ) (H : A→ℝ) (e : ℝ)
    (hF : Integrable F (μ.prod (ν.prod ρ))) (hG : Integrable G (μ.prod (ν.prod ρ)))
    (hH : Integrable H μ)
    (h : ∀ a b,(∫ c,G (a,b,c) ∂ρ)-H a-e≤∫ c,F (a,b,c) ∂ρ) :
    (∫ p,G p ∂μ.prod (ν.prod ρ))-(∫ a,H a ∂μ)-e≤∫ p,F p ∂μ.prod (ν.prod ρ) := by
  have hp:=measurePreserving_prodAssoc μ ν ρ
  have hFi:= (hp.integrable_comp hF.aestronglyMeasurable).mpr hF
  have hGi:= (hp.integrable_comp hG.aestronglyMeasurable).mpr hG
  have hHi:=hH.comp_fst ν
  have hi:=integral_mono ((hGi.integral_prod_left.sub hHi).sub (integrable_const e))
    hFi.integral_prod_left (fun p=>h p.1 p.2)
  erw [integral_sub (hGi.integral_prod_left.sub hHi) (integrable_const e),
    integral_sub hGi.integral_prod_left hHi,integral_const,probReal_univ,one_smul,
    integral_fun_fst,probReal_univ,one_smul,←integral_prod _ hGi,←integral_prod _ hFi] at hi
  have hfe:=cavity_integral_preserving _ _ _ hp F hF.aestronglyMeasurable
  have hge:=cavity_integral_preserving _ _ _ hp G hG.aestronglyMeasurable
  simp only [Function.comp_def] at hi
  rw [hfe,hge] at hi
  exact hi

def cavityOldError (n k M d : ℕ) (f : Jet3)
    (h1 : HasCompactSupport (f.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (f.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (f.d3 : ℝ→ℝ)) : ℝ :=
  let K : ℝ:=M/(n+1:ℕ)*‖f.dilationMark h1‖
  K/2+
    Real.exp (2*(d*‖f.f‖+((k+1:ℕ)+1)*K/2)+(Real.sqrt (n+1:ℕ))⁻¹^2*((k+1:ℕ)+1)^2*M*‖f.d1‖^2)*
      Real.sqrt ((1/(2*(n+1:ℕ)))^2*(((k+1:ℕ)+1)^2)^2*squareGaussianVariance*M*‖f.d2‖^2)+
    (∫ y : Fin M→Spin (k+1),∑ i,cavityRemainderMajorant
      (cavityRemainderCoefficients f h1 h2 h3 (k+1) ((k+1)+1)) (n+1:ℕ) ‖y i‖
      ∂Measure.pi (fun _=>stdGaussian (Spin (k+1))))

lemma cavitySplitLog_proxy_integrable (n k M d : ℕ) (f : Jet3)
    (hf : HasCompactSupport (f.d1 : ℝ→ℝ)) (v : ℕ→ℝ) :
    Integrable (fun p : CavityProxyRandom n (k+1) M d=>Real.log (cavitySplitPartition k d n M f v (p.1,p.2.2,p.2.1)))
      (cavityProxyLaw n (k+1) M d) := by
  have : IsProbabilityMeasure (finitePatternRowsLaw (n+1) d) := inferInstance
  have : IsProbabilityMeasure (Measure.pi fun _ : Fin M=>stdGaussian (Spin (k+1))) := inferInstance
  have : SFinite (finitePatternRowsLaw (n+1) d) := inferInstance
  have : SFinite (Measure.pi fun _ : Fin M=>stdGaussian (Spin (k+1))) := inferInstance
  have hp:=(MeasurePreserving.id (bulkDisorderLaw (n+1) M)).prod
    (Measure.measurePreserving_swap (μ:=finitePatternRowsLaw (n+1) d)
      (ν:=Measure.pi fun _ : Fin M=>stdGaussian (Spin (k+1))))
  exact (hp.integrable_comp (cavitySplitPartition_measurable k d n M f v).log.aestronglyMeasurable).mpr
    (cavitySplitLog_integrable k d n M f hf v)

lemma cavity_proxy_conditional_lower (n k M d : ℕ) (f : Jet3)
    (h1 : HasCompactSupport (f.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (f.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (f.d3 : ℝ→ℝ)) (hn : 2*((k+1)+1)≤n+1)
    (hp : (cavitySphereLaw n (k+1) : Measure (Spin (k+1))) (cavityShell (k+1))≠0) (v : ℕ→ℝ)
    (a : BulkDisorder (n+1) M) (b : Fin d→Fin (n+1)→ℝ) :
    (∫ y, Real.log (cavitySplitPartition k d n M f v (a,y,b)) ∂Measure.pi (fun _ : Fin M=>stdGaussian (Spin (k+1))))
      -(-bulkLogPartition n M f.f v a.1 a.2)-cavityOldError n k M d f h1 h2 h3≤
      ∫ y,cavityProxyLog n (k+1) M d f v (a,b,y) ∂Measure.pi (fun _ : Fin M=>stdGaussian (Spin (k+1))) := by
  have hw : Measurable (normalizedPatternEnergy (n+1) d f.f b) :=
    (normalizedPatternEnergy_continuous (n+1) d f.f).measurable.comp (f:=fun x : NormalizedSpin (n+1)=>(b,x)) (measurable_const.prodMk measurable_id)
  have hi:= cavity_normalized_old_increment_lower n k M f h1 h2 h3 hn hp v a
    (normalizedPatternEnergy (n+1) d f.f b) hw (by positivity : 0≤d*‖f.f‖)
    (normalizedPatternEnergy_bound (n+1) d f.f b)
  dsimp only at hi
  have hsec:=cavityProxyLog_section_integrable n (k+1) M d f v hp a b
  change _≤∫ y,cavityProxyLog n (k+1) M d f v (a,b,y)-bulkLogPartition n M f.f v a.1 a.2 ∂Measure.pi (fun _ : Fin M=>stdGaussian (Spin (k+1))) at hi
  rw [integral_sub hsec (integrable_const _),integral_const,probReal_univ,one_smul] at hi
  dsimp only [cavityOldError]
  change (∫ y,Real.log (cavitySplitPartition k d n M f v (a,y,b)) ∂Measure.pi (fun _=>stdGaussian (Spin (k+1))))-_-_-_≤_ at hi
  linarith

lemma cavity_proxy_expected_lower (n k M d : ℕ) (f : Jet3)
    (h1 : HasCompactSupport (f.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (f.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (f.d3 : ℝ→ℝ)) (hn : 2*((k+1)+1)≤n+1)
    (hp : (cavitySphereLaw n (k+1) : Measure (Spin (k+1))) (cavityShell (k+1))≠0) (v : ℕ→ℝ) :
    cavityBulkFullLog k d n M f v+bulkExpectedLog n M f.f v-cavityOldError n k M d f h1 h2 h3≤
      ∫ p,cavityProxyLog n (k+1) M d f v p ∂cavityProxyLaw n (k+1) M d := by
  let F:=cavityProxyLog n (k+1) M d f v
  let G:=fun p : CavityProxyRandom n (k+1) M d=>Real.log (cavitySplitPartition k d n M f v (p.1,p.2.2,p.2.1))
  let H:=fun a : BulkDisorder (n+1) M=> -bulkLogPartition n M f.f v a.1 a.2
  have hFi:=cavityProxyLog_integrable n (k+1) M d f v hp
  have hGi:=cavitySplitLog_proxy_integrable n k M d f h1 v
  have hHi:=((bulkLogPartition_memLp n M f.f v).integrable (by norm_num)).neg
  have hi:=cavity_three_integral_compare (bulkDisorderLaw (n+1) M) (finitePatternRowsLaw (n+1) d)
    (Measure.pi fun _ : Fin M=>stdGaussian (Spin (k+1))) F G H (cavityOldError n k M d f h1 h2 h3)
    hFi hGi hHi (fun a b=>?_)
  · have he: (∫ p,G p ∂cavityProxyLaw n (k+1) M d)=cavityBulkFullLog k d n M f v := by
      unfold cavityProxyLaw
      rw [cavity_three_integral _ _ _ G hGi,cavityBulkFullLog_split k d n M f h1 v]
    have hh: (∫ a,H a ∂bulkDisorderLaw (n+1) M)= -bulkExpectedLog n M f.f v := integral_neg _
    change (∫ p,G p ∂cavityProxyLaw n (k+1) M d)-(∫ a,H a ∂bulkDisorderLaw (n+1) M)-_≤_ at hi
    rw [he,hh,sub_neg_eq_add] at hi
    exact hi
  · exact cavity_proxy_conditional_lower n k M d f h1 h2 h3 hn hp v a b


lemma cavity_actual_proxy_log_bound (n L M d : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0)
    (p : CavityIncrementRandom n L M d) :
    |cavityShellLowLog n L (M+d) f.f v (cavityIncrementFullRows n L M d p,p.1.2)-
      cavityProxyLog n L M d f v (cavityProxyProjection n L M d p)|≤
        cavityFreshMajorant (n+1) L d f p.2.1 p.2.2.2 := by
  let H:=fun s : CavityShellSpin n L=>cavityShellPatternEnergy n L M f.f
    (cavityJoinedPatterns (n+1) L M p.1.1 p.2.2.1) s+inner ℝ (bulkFeature (n+1) v s.1) p.1.2
  have hm : Measurable H := (cavityShellPatternEnergy_measurable n L M f.f _).add
    (((bulkFeature_continuous (n+1) v).measurable.comp measurable_fst).inner measurable_const)
  have hb : ∀ s,|H s|≤M*‖f.f‖+bulkFeatureBound (n+1) v*‖p.1.2‖ := by
    intro s
    exact (abs_add_le _ _).trans (add_le_add (cavityShellPatternEnergy_bound n L M f.f _ s)
      (by simpa only [bulkFeature_norm] using abs_real_inner_le_norm (bulkFeature (n+1) v s.1) p.1.2))
  have hh:=cavity_fresh_log_replacement n L d f hp H hm
    (show 0≤M*‖f.f‖+bulkFeatureBound (n+1) v*‖p.1.2‖ from by unfold bulkFeatureBound; positivity)
    hb p.2.1 p.2.2.2
  convert hh using 1
  congr 2
  unfold cavityShellLowLog tiltPartition cavityIncrementFullRows
  simp_rw [one_mul,cavityShellPatternEnergy_append]
  congr 2
  funext s
  congr 1
  dsimp only [H]
  ring

lemma cavityFreshProjection_preserving (n L M d : ℕ) :
    MeasurePreserving (fun p : CavityIncrementRandom n L M d=>(p.2.1,p.2.2.2))
      (cavityIncrementLaw n L M d)
      ((finitePatternRowsLaw (n+1) d).prod (Measure.pi fun _ : Fin d=>stdGaussian (Spin L))) := by
  have : IsProbabilityMeasure (finitePatternRowsLaw (n+1) d) := inferInstance
  have : SFinite (finitePatternRowsLaw (n+1) d) := inferInstance
  have h1 : MeasurePreserving Prod.snd (cavityIncrementLaw n L M d)
      ((finitePatternRowsLaw (n+1) d).prod ((Measure.pi fun _ : Fin M=>stdGaussian (Spin L)).prod
        (Measure.pi fun _ : Fin d=>stdGaussian (Spin L)))) := measurePreserving_snd
  have h2 : MeasurePreserving Prod.snd
      ((Measure.pi fun _ : Fin M=>stdGaussian (Spin L)).prod (Measure.pi fun _ : Fin d=>stdGaussian (Spin L)))
      (Measure.pi fun _ : Fin d=>stdGaussian (Spin L)) := measurePreserving_snd
  exact ((MeasurePreserving.id (finitePatternRowsLaw (n+1) d)).prod h2).comp h1

lemma cavity_fresh_expected_lower (n L M d : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    (∫ p,cavityProxyLog n L M d f v p ∂cavityProxyLaw n L M d)-
      ‖f.d1‖*d*((L:ℝ)+1)*(1+Real.sqrt L)/Real.sqrt (n+1:ℕ)≤
    ∫ p,cavityShellLowLog n L (M+d) f.f v p
      ∂(finitePatternRowsLaw (n+1+L) (M+d)).prod (stdGaussian (BulkMark (n+1))) := by
  let F:=fun p : CavityIncrementRandom n L M d=>
    cavityShellLowLog n L (M+d) f.f v (cavityIncrementFullRows n L M d p,p.1.2)
  let G:=fun p : CavityIncrementRandom n L M d=>cavityProxyLog n L M d f v (cavityProxyProjection n L M d p)
  let R:=fun p : CavityIncrementRandom n L M d=>cavityFreshMajorant (n+1) L d f p.2.1 p.2.2.2
  have hF:=cavityIncrement_actual_integrable n L M d f.f v hp
  have hG : Integrable G (cavityIncrementLaw n L M d) := (cavityProxyProjection_preserving n L M d).integrable_comp_of_integrable
    (cavityProxyLog_integrable n L M d f v hp)
  have hr:=cavityFreshMajorant_rows_integrable (n+1) L d f
  have hR : Integrable R (cavityIncrementLaw n L M d) := (cavityFreshProjection_preserving n L M d).integrable_comp_of_integrable hr
  have hi:=integral_mono (hG.sub hR) hF (fun p=>by
    have hb:=(abs_le.mp (cavity_actual_proxy_log_bound n L M d f v hp p)).1
    change G p-R p≤F p
    dsimp only [F,G,R]
    linarith)
  change (∫ p,G p-R p ∂cavityIncrementLaw n L M d)≤∫ p,F p ∂cavityIncrementLaw n L M d at hi
  rw [integral_sub hG hR] at hi
  have heG:=cavity_integral_preserving _ _ _ (cavityProxyProjection_preserving n L M d) _
    (cavityProxyLog_measurable n L M d f v hp).aestronglyMeasurable
  have heR:=cavity_integral_preserving _ _ _ (cavityFreshProjection_preserving n L M d) _ hr.aestronglyMeasurable
  change (∫ p,G p ∂cavityIncrementLaw n L M d)=_ at heG
  change (∫ p,R p ∂cavityIncrementLaw n L M d)=_ at heR
  rw [heG,heR] at hi
  have heF:=cavityIncrement_actual_expectation n L M d f.f v hp
  change (∫ p,F p ∂cavityIncrementLaw n L M d)=_ at heF
  rw [heF] at hi
  exact (sub_le_sub_left (cavityFreshMajorant_rows_mean_bound n L d f) _).trans hi
end SphericalPerceptronFreeEnergy

end

end OAI
