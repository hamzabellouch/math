import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityFreshReplacement
import OAI.Probability.Perceptron.Cavity.CavityNormalizedIncrement
import OAI.Probability.Perceptron.Cavity.CavityProductLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

abbrev CavityIncrementRandom (n L M d : ℕ) :=
  BulkDisorder (n+1) M×(Fin d→Fin (n+1)→ℝ)×(Fin M→Spin L)×(Fin d→Spin L)

def cavityIncrementLaw (n L M d : ℕ) : Measure (CavityIncrementRandom n L M d) :=
  (bulkDisorderLaw (n+1) M).prod ((finitePatternRowsLaw (n+1) d).prod
    ((Measure.pi fun _ : Fin M=>stdGaussian (Spin L)).prod (Measure.pi fun _ : Fin d=>stdGaussian (Spin L))))

instance (n L M d : ℕ) : IsProbabilityMeasure (cavityIncrementLaw n L M d) := by
  unfold cavityIncrementLaw
  infer_instance

def cavityIncrementFullRows (n L M d : ℕ) (p : CavityIncrementRandom n L M d) :
    Fin (M+d)→Fin (n+1+L)→ℝ :=
  cavityRowsAppend (n+1+L) M d (cavityJoinedPatterns (n+1) L M p.1.1 p.2.2.1)
    (cavityJoinedPatterns (n+1) L d p.2.1 p.2.2.2)

lemma cavityIncrementFullRows_preserving (n L M d : ℕ) :
    MeasurePreserving (fun p : CavityIncrementRandom n L M d=>(cavityIncrementFullRows n L M d p,p.1.2))
      (cavityIncrementLaw n L M d)
      ((finitePatternRowsLaw (n+1+L) (M+d)).prod (stdGaussian (BulkMark (n+1)))) := by
  let : IsProbabilityMeasure (stdGaussian (BulkMark (n+1))) := inferInstance
  let : IsProbabilityMeasure (finitePatternRowsLaw (n+1) M) := inferInstance
  let : IsProbabilityMeasure (finitePatternRowsLaw (n+1) d) := inferInstance
  let : IsProbabilityMeasure (Measure.pi fun _ : Fin M=>stdGaussian (Spin L)) := inferInstance
  let : IsProbabilityMeasure (Measure.pi fun _ : Fin d=>stdGaussian (Spin L)) := inferInstance
  let : IsProbabilityMeasure (finitePatternRowsLaw (n+1+L) M) := inferInstance
  let : IsProbabilityMeasure (finitePatternRowsLaw (n+1+L) d) := inferInstance
  let : SFinite (stdGaussian (BulkMark (n+1))) := inferInstance
  let : SFinite (finitePatternRowsLaw (n+1) d) := inferInstance
  have h1 := cavity_product_shuffle (finitePatternRowsLaw (n+1) M) (stdGaussian (BulkMark (n+1)))
    (finitePatternRowsLaw (n+1) d) (Measure.pi fun _ : Fin M=>stdGaussian (Spin L))
    (Measure.pi fun _ : Fin d=>stdGaussian (Spin L))
  let : SFinite ((finitePatternRowsLaw (n+1) M).prod (Measure.pi fun _ : Fin M=>stdGaussian (Spin L))) := inferInstance
  let : SFinite ((finitePatternRowsLaw (n+1) d).prod (Measure.pi fun _ : Fin d=>stdGaussian (Spin L))) := inferInstance
  have hOld : MeasurePreserving (fun p=>(cavityJoinedPatterns (n+1) L M p.1 p.2))
      ((finitePatternRowsLaw (n+1) M).prod (Measure.pi fun _ : Fin M=>stdGaussian (Spin L)))
      (finitePatternRowsLaw (n+1+L) M) := cavityJoinedPatterns_preserving (n+1) L M
  have hNew : MeasurePreserving (fun p=>(cavityJoinedPatterns (n+1) L d p.1 p.2))
      ((finitePatternRowsLaw (n+1) d).prod (Measure.pi fun _ : Fin d=>stdGaussian (Spin L)))
      (finitePatternRowsLaw (n+1+L) d) := cavityJoinedPatterns_preserving (n+1) L d
  have h2 := hOld.prod hNew
  have h3 := h2.prod (MeasurePreserving.id (stdGaussian (BulkMark (n+1))))
  have h4 := (cavityRowsAppend_preserving (n+1+L) M d).prod
    (MeasurePreserving.id (stdGaussian (BulkMark (n+1))))
  exact h4.comp (h3.comp h1)

lemma cavityShellLowLog_measurable (n L M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    Measurable (cavityShellLowLog n L M f v) := by
  let :=cavityShellBaseLaw_probability n L hp
  have hH : Measurable (fun p : ((Fin M→Fin (n+1+L)→ℝ)×BulkMark (n+1))×CavityShellSpin n L=>
      cavityShellPatternEnergy n L M f p.1.1 p.2+inner ℝ (bulkFeature (n+1) v p.2.1) p.1.2) :=
    ((cavityShellPatternEnergy_joint_measurable n L M f).comp
      (measurable_fst.fst.prodMk measurable_snd)).add
      (((bulkFeature_continuous (n+1) v).measurable.comp measurable_snd.fst).inner measurable_fst.snd)
  unfold cavityShellLowLog tiltPartition
  simpa only [one_mul] using
    (hH.exp.stronglyMeasurable.integral_prod_right' (ν:=cavityShellBaseLaw n L)).measurable.log

lemma cavityIncrement_actual_integrable (n L M d : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    Integrable (fun p : CavityIncrementRandom n L M d=>
      cavityShellLowLog n L (M+d) f v (cavityIncrementFullRows n L M d p,p.1.2))
        (cavityIncrementLaw n L M d) :=
  ((cavityIncrementFullRows_preserving n L M d).integrable_comp
    (cavityShellLowLog_measurable n L (M+d) f v hp).aestronglyMeasurable).mpr
      (cavityShellLowLog_integrable n L (M+d) f v hp)

lemma cavityIncrement_actual_expectation (n L M d : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    (∫ p : CavityIncrementRandom n L M d,
      cavityShellLowLog n L (M+d) f v (cavityIncrementFullRows n L M d p,p.1.2)
        ∂cavityIncrementLaw n L M d)=
      ∫ p,cavityShellLowLog n L (M+d) f v p
        ∂(finitePatternRowsLaw (n+1+L) (M+d)).prod (stdGaussian (BulkMark (n+1))) :=
  cavity_integral_preserving _ _ _ (cavityIncrementFullRows_preserving n L M d) _
    (cavityShellLowLog_measurable n L (M+d) f v hp).aestronglyMeasurable

lemma finiteRows_toLp_preserving (N d : ℕ) :
    MeasurePreserving (fun a : Fin d→Fin N→ℝ=>fun i=>WithLp.toLp 2 (a i))
      (finitePatternRowsLaw N d) (Measure.pi fun _ : Fin d=>stdGaussian (Spin N)) := by
  apply measurePreserving_pi
  intro i
  exact ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩

lemma cavityFreshMajorant_rows_integrable (N L d : ℕ) (f : Jet3) :
    Integrable (fun p : (Fin d→Fin N→ℝ)×(Fin d→Spin L)=>cavityFreshMajorant N L d f p.1 p.2)
      ((finitePatternRowsLaw N d).prod (Measure.pi fun _ : Fin d=>stdGaussian (Spin L))) := by
  have hi:=cavityFreshMajorant_integrable N L d f
  have hp:=(finiteRows_toLp_preserving N d).prod (MeasurePreserving.id (Measure.pi fun _ : Fin d=>stdGaussian (Spin L)))
  convert (hp.integrable_comp hi.aestronglyMeasurable).mpr hi using 1
  rfl

lemma cavityFreshMajorant_rows_mean_bound (n L d : ℕ) (f : Jet3) :
    (∫ p : (Fin d→Fin (n+1)→ℝ)×(Fin d→Spin L),cavityFreshMajorant (n+1) L d f p.1 p.2
      ∂(finitePatternRowsLaw (n+1) d).prod (Measure.pi fun _ : Fin d=>stdGaussian (Spin L)))≤
      ‖f.d1‖*d*((L:ℝ)+1)*(1+Real.sqrt L)/Real.sqrt (n+1:ℕ) := by
  let : IsProbabilityMeasure (finitePatternRowsLaw (n+1) d) := inferInstance
  let : IsProbabilityMeasure (Measure.pi fun _ : Fin d=>stdGaussian (Spin L)) := inferInstance
  let : SFinite (finitePatternRowsLaw (n+1) d) := inferInstance
  have hi:=cavityFreshMajorant_integrable (n+1) L d f
  have hp:=(finiteRows_toLp_preserving (n+1) d).prod (MeasurePreserving.id (Measure.pi fun _ : Fin d=>stdGaussian (Spin L)))
  have h:=cavity_integral_preserving _ _ _ hp _ hi.aestronglyMeasurable
  exact (Eq.trans (by rfl) h).le.trans (cavityFreshMajorant_mean_bound n L d f)

abbrev CavityProxyRandom (n L M d : ℕ) := BulkDisorder (n+1) M×(Fin d→Fin (n+1)→ℝ)×(Fin M→Spin L)
def cavityProxyLaw (n L M d : ℕ) : Measure (CavityProxyRandom n L M d) :=
  (bulkDisorderLaw (n+1) M).prod ((finitePatternRowsLaw (n+1) d).prod (Measure.pi fun _ : Fin M=>stdGaussian (Spin L)))
instance (n L M d : ℕ) : IsProbabilityMeasure (cavityProxyLaw n L M d) := by
  unfold cavityProxyLaw; infer_instance

def cavityProxyProjection (n L M d : ℕ) (p : CavityIncrementRandom n L M d) : CavityProxyRandom n L M d :=
  (p.1,p.2.1,p.2.2.1)
lemma cavityProxyProjection_preserving (n L M d : ℕ) :
    MeasurePreserving (cavityProxyProjection n L M d) (cavityIncrementLaw n L M d) (cavityProxyLaw n L M d) :=
  (MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod measurePreserving_fst)

def cavityProxyHamiltonian (n L M d : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (p : CavityProxyRandom n L M d) (s : CavityShellSpin n L) : ℝ :=
  cavityOldJoinedHamiltonian n L M f v p.1 (normalizedPatternEnergy (n+1) d f.f p.2.1) p.2.2 s

def cavityProxyLog (n L M d : ℕ) (f : Jet3) (v : ℕ→ℝ) (p : CavityProxyRandom n L M d) : ℝ :=
  Real.log (∫ s,Real.exp (cavityProxyHamiltonian n L M d f v p s) ∂cavityShellBaseLaw n L)

lemma cavityProxyHamiltonian_measurable (n L M d : ℕ) (f : Jet3) (v : ℕ→ℝ) :
    Measurable (fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>cavityProxyHamiltonian n L M d f v p.1 p.2) := by
  have hj : Measurable (fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>
      cavityJoinedPatterns (n+1) L M p.1.1.1 p.1.2.2) :=
    (cavityJoinedPatterns_preserving (n+1) L M).measurable.comp
      (f:=fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>(p.1.1.1,p.1.2.2))
      (measurable_fst.fst.fst.prodMk measurable_fst.snd.snd)
  have hs : Measurable (fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>
      cavityShellPatternEnergy n L M f.f (cavityJoinedPatterns (n+1) L M p.1.1.1 p.1.2.2) p.2) :=
    (cavityShellPatternEnergy_joint_measurable n L M f.f).comp
      (f:=fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>(cavityJoinedPatterns (n+1) L M p.1.1.1 p.1.2.2,p.2))
      (hj.prodMk measurable_snd)
  have hm : Measurable (fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>
      inner ℝ (bulkFeature (n+1) v p.2.1) p.1.1.2) :=
    (((bulkFeature_continuous (n+1) v).measurable.comp
      (f:=fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>p.2.1) measurable_snd.fst).inner measurable_fst.fst.snd)
  have hn : Measurable (fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>
      normalizedPatternEnergy (n+1) d f.f p.1.2.1 p.2.1) :=
    (normalizedPatternEnergy_continuous (n+1) d f.f).measurable.comp
      (f:=fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>(p.1.2.1,p.2.1))
      (measurable_fst.snd.fst.prodMk measurable_snd.fst)
  unfold cavityProxyHamiltonian cavityOldJoinedHamiltonian
  exact (hs.add hm).add hn

lemma cavityProxyLog_measurable (n L M d : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    Measurable (cavityProxyLog n L M d f v) := by
  let :=cavityShellBaseLaw_probability n L hp
  exact (cavityProxyHamiltonian_measurable n L M d f v).exp.stronglyMeasurable.integral_prod_right'.measurable.log

lemma cavityProxyHamiltonian_bound (n L M d : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (p : CavityProxyRandom n L M d) (s : CavityShellSpin n L) :
    |cavityProxyHamiltonian n L M d f v p s|≤(M+d)*‖f.f‖+bulkFeatureBound (n+1) v*‖p.1.2‖ := by
  unfold cavityProxyHamiltonian cavityOldJoinedHamiltonian
  exact ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
    (add_le_add (cavityShellPatternEnergy_bound n L M f.f _ s)
      (by simpa only [bulkFeature_norm] using abs_real_inner_le_norm (bulkFeature (n+1) v s.1) p.1.2)))
        (normalizedPatternEnergy_bound (n+1) d f.f _ _))).trans_eq (by ring)

lemma cavityProxyLog_integrable (n L M d : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    Integrable (cavityProxyLog n L M d f v) (cavityProxyLaw n L M d) := by
  let :=cavityShellBaseLaw_probability n L hp
  have hb : Integrable (fun p : BulkDisorder (n+1) M=>‖p.2‖) (bulkDisorderLaw (n+1) M) :=
    (IsGaussian.integrable_id (μ:=stdGaussian (BulkMark (n+1)))).norm.comp_snd (finitePatternRowsLaw (n+1) M)
  have hg : Integrable (fun p : CavityProxyRandom n L M d=>‖p.1.2‖) (cavityProxyLaw n L M d) :=
    hb.comp_fst ((finitePatternRowsLaw (n+1) d).prod (Measure.pi fun _ : Fin M=>stdGaussian (Spin L)))
  have hm : Measurable (fun p : CavityShellSpin n L×CavityProxyRandom n L M d=>
      cavityProxyHamiltonian n L M d f v p.2 p.1) :=
    (cavityProxyHamiltonian_measurable n L M d f v).comp
      (f:=fun p : CavityShellSpin n L×CavityProxyRandom n L M d=>(p.2,p.1)) measurable_swap
  unfold cavityProxyLog
  apply cavity_log_integrable_of_bound (cavityShellBaseLaw n L) (cavityProxyLaw n L M d)
    (fun p=>cavityProxyHamiltonian n L M d f v p.2 p.1)
    hm
    (fun p=>(M+d)*‖f.f‖+bulkFeatureBound (n+1) v*‖p.1.2‖)
    ((integrable_const _).add (hg.const_mul _))
    (fun p=>by unfold bulkFeatureBound; positivity)
  intro s p
  exact cavityProxyHamiltonian_bound n L M d f v p s

lemma cavityProxyLog_section_integrable (n L M d : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0)
    (a : BulkDisorder (n+1) M) (b : Fin d→Fin (n+1)→ℝ) :
    Integrable (fun y=>cavityProxyLog n L M d f v (a,b,y)) (Measure.pi fun _ : Fin M=>stdGaussian (Spin L)) := by
  let :=cavityShellBaseLaw_probability n L hp
  have hm : Measurable (fun p : CavityShellSpin n L×(Fin M→Spin L)=>
      cavityProxyHamiltonian n L M d f v (a,b,p.2) p.1) :=
    (cavityProxyHamiltonian_measurable n L M d f v).comp
      (f:=fun p : CavityShellSpin n L×(Fin M→Spin L)=>((a,b,p.2),p.1))
      ((measurable_const.prodMk (measurable_const.prodMk measurable_snd)).prodMk measurable_fst)
  unfold cavityProxyLog
  apply cavity_log_integrable_of_bound (cavityShellBaseLaw n L) (Measure.pi fun _ : Fin M=>stdGaussian (Spin L))
    (fun p=>cavityProxyHamiltonian n L M d f v (a,b,p.2) p.1)
    hm
    (fun _=>(M+d)*‖f.f‖+bulkFeatureBound (n+1) v*‖a.2‖) (integrable_const _)
    (fun _=>by unfold bulkFeatureBound; positivity)
  intro s y
  exact cavityProxyHamiltonian_bound n L M d f v (a,b,y) s
end SphericalPerceptronFreeEnergy

end

end OAI
