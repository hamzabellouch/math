import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityExpectedCompensator
import OAI.Probability.Perceptron.Cavity.CavityAnnealedUncap
import OAI.Probability.Perceptron.Sphere.GaussianCoordinateProjection

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction

def cavityBulkFullLog (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) : ℝ :=
  ∫ p,Real.log (cavityBulkFullCompPartition n d m M f v p)
    ∂(bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))

lemma cavityBulk_log_integrable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ) :
    Integrable (fun p=>Real.log (cavityBulkPartition n d m M f v Λ hΛ p))
      ((bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))) := by
  apply Integrable.of_bound (cavityBulkPartition_measurable n d m M f v Λ hΛ).log.aestronglyMeasurable
    ‖cavityPartitionLogTest d f.f Λ‖
  exact ae_of_all _ fun p=>(cavityPartitionLogTest d f.f Λ).norm_coe_le_norm
    ⟨cavityBulkPartition n d m M f v Λ hΛ p,cavityBulkPartition_mem n d m M f v Λ hΛ p⟩

lemma cavityBulk_comp_log_integrable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (K : ℝ) (hK : 0≤K)
    (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤K) :
    Integrable (fun p=>Real.log (cavityBulkCompPartition n d m M f v Λ hΛ p))
      ((bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))) := by
  have he:=cavityBulkCompError_integrable n d m M f v Λ hΛ 0 K (by simpa using hK) hC
  have hb:=cavityBulk_log_integrable n d m M f v Λ hΛ
  exact (he.add hb).congr (ae_of_all _ fun p=>by dsimp [cavityBulkCompError]; ring)

lemma cavityBulk_full_log_integrable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (K KC : ℝ) (hK : M/(m+1:ℕ)*‖f.d1‖^2≤K) (hKC : 0≤KC)
    (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤KC) :
    Integrable (fun p=>Real.log (cavityBulkFullCompPartition n d m M f v p))
      ((bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))) := by
  have he:=(cavityBulk_uncap_annealed n d m M f v 1 le_rfl K KC hK hC).1
  have hb:=cavityBulk_comp_log_integrable n d m M f v 1 le_rfl KC hKC hC
  exact (he.add hb).congr (ae_of_all _ fun p=>by dsimp [cavityBulkUncapError]; ring)

lemma cavityBulkFullLog_decomposition (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (c K KC : ℝ) (hc : |c|≤KC)
    (hK : M/(m+1:ℕ)*‖f.d1‖^2≤K)
    (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤KC) :
    let Q:=(bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))
    cavityBulkFullLog n d m M f v=
      (∫ p,cavityBulkUncapError n d m M f v Λ hΛ p ∂Q)+
      (∫ p,cavityBulkCompError n d m M f v Λ hΛ c p ∂Q)+
      ((n+1:ℕ)/2*c+cavityBulkLog n d m M f v Λ hΛ) := by
  have hKC : 0≤KC:=(abs_nonneg c).trans hc
  have hi:=cavityBulk_full_log_integrable n d m M f v K KC hK hKC hC
  have hj:=cavityBulk_comp_log_integrable n d m M f v Λ hΛ KC hKC hC
  have hk:=cavityBulk_log_integrable n d m M f v Λ hΛ
  dsimp only
  unfold cavityBulkUncapError cavityBulkCompError
  have hs:=integral_sub hj ((integrable_const ((n+1:ℕ)/2*c)).add hk)
  have ha:=integral_add (integrable_const ((n+1:ℕ)/2*c)) hk
  simp only [Pi.add_apply] at hs ha
  rw [integral_sub hi hj,hs,ha,integral_const,probReal_univ,one_smul,integral_prod _ hk]
  unfold cavityBulkFullLog cavityBulkLog
  ring

def cavityBulkNoiseJoin (n d m M : ℕ)
    (p : (Fin M→Spin (n+1))×(Fin d→Fin (m+1)→ℝ)) :
    EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M) :=
  WithLp.toLp 2 (fun j=> match j with
    | (Sum.inl i,Sum.inl t)=>p.1 t i
    | (Sum.inr t,Sum.inr i)=>p.2 t i
    | _=>0)

lemma cavityBulkNoiseJoin_measurable (n d m M : ℕ) :
    Measurable (cavityBulkNoiseJoin n d m M) := by
  apply (MeasurableEquiv.toLp 2 _).measurable.comp
  apply Measurable.of_eval
  intro j
  rcases j with ⟨i,t⟩
  cases i <;> cases t <;> dsimp [cavityBulkNoiseJoin] <;> fun_prop

lemma cavityBulkNoiseSplit_join (n d m M : ℕ)
    (p : (Fin M→Spin (n+1))×(Fin d→Fin (m+1)→ℝ)) :
    cavityBulkNoiseSplit n d m M (cavityBulkNoiseJoin n d m M p)=p := by
  rfl

def cavitySplitPartition (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (p : BulkDisorder (m+1) M×((Fin M→Spin (n+1))×(Fin d→Fin (m+1)→ℝ))) : ℝ :=
  ∫ x,Real.exp (normalizedPatternEnergy (m+1) d f.f p.2.2 x+
    (n+1:ℕ)*bulkC (m+1) M f p.1.1 x/2)*
    sphericalExp n (cavityVectorField M (n+1) (fun t=>f.d1 (∑ i,p.1.1 t i*x.val i))
      (Real.sqrt (m+1:ℕ))⁻¹ p.2.1) (Real.sqrt (n+1:ℕ))
    ∂tiltLaw (unitSphereLaw (m+1)) (bulkHamiltonian (m+1) M f.f v p.1.1 p.1.2) 1

lemma cavitySplitPartition_identity (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (a : BulkDisorder (m+1) M) (y : EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) :
    cavityBulkFullCompPartition n d m M f v (a,y)=
      cavitySplitPartition n d m M f v (a,cavityBulkNoiseSplit n d m M y) := by
  unfold cavitySplitPartition
  rw [tilt_law_integral _ (bulkHamiltonian_section_measurable (m+1) M f.f v a)
    (show 0≤M*‖f.f‖+bulkFeatureBound (m+1) v*‖a.2‖ from by
      unfold bulkFeatureBound; positivity) (bulkHamiltonian_bound (m+1) M f.f v a) 1]
  unfold cavityBulkFullCompPartition
  congr 1
  funext x
  rw [cavityBulkNoiseSplit_vector]
  simp_rw [cavityBulkNoiseSplit_scalar]
  congr 2
  unfold normalizedPatternEnergy
  ring

lemma cavitySplitPartition_measurable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) :
    Measurable (cavitySplitPartition n d m M f v) := by
  have hm:=(cavityBulkFullCompPartition_measurable n d m M f v).comp
    (measurable_fst.prodMk ((cavityBulkNoiseJoin_measurable n d m M).comp measurable_snd))
  simpa only [Function.comp_def,cavitySplitPartition_identity,cavityBulkNoiseSplit_join] using hm

lemma cavitySplitLog_integrable (n d m M : ℕ) (f : Jet3)
    (hf : HasCompactSupport (f.d1 : ℝ→ℝ)) (v : ℕ→ℝ) :
    Integrable (fun p=>Real.log (cavitySplitPartition n d m M f v p))
      ((bulkDisorderLaw (m+1) M).prod ((Measure.pi fun _ : Fin M=>stdGaussian (Spin (n+1))).prod
        (finitePatternRowsLaw (m+1) d))) := by
  have hp:=(MeasurePreserving.id (bulkDisorderLaw (m+1) M)).prod (cavityBulkNoiseSplit_preserving n d m M)
  apply (hp.integrable_comp (cavitySplitPartition_measurable n d m M f v).log.aestronglyMeasurable).mp
  have hi:=cavityBulk_full_log_integrable n d m M f v
    (M/(m+1:ℕ)*‖f.d1‖^2) (M/(m+1:ℕ)*‖f.dilationMark hf‖) le_rfl (by positivity)
    (bulkC_bound m M f hf)
  convert hi using 1
  funext p
  exact congrArg Real.log (cavitySplitPartition_identity n d m M f v p.1 p.2).symm

lemma cavityBulkFullLog_split (n d m M : ℕ) (f : Jet3)
    (hf : HasCompactSupport (f.d1 : ℝ→ℝ)) (v : ℕ→ℝ) :
    cavityBulkFullLog n d m M f v=
      ∫ a,∫ b,∫ y,Real.log (cavitySplitPartition n d m M f v (a,y,b))
        ∂Measure.pi (fun _ : Fin M=>stdGaussian (Spin (n+1)))
        ∂finitePatternRowsLaw (m+1) d ∂bulkDisorderLaw (m+1) M := by
  have hp:=(MeasurePreserving.id (bulkDisorderLaw (m+1) M)).prod (cavityBulkNoiseSplit_preserving n d m M)
  have h : (∫ p,Real.log (cavitySplitPartition n d m M f v (Prod.map id (cavityBulkNoiseSplit n d m M) p))
      ∂(bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M))))=
      ∫ p,Real.log (cavitySplitPartition n d m M f v p)
        ∂(bulkDisorderLaw (m+1) M).prod ((Measure.pi fun _ : Fin M=>stdGaussian (Spin (n+1))).prod
          (finitePatternRowsLaw (m+1) d)) := by
    rw [←hp.map_eq]
    exact (integral_map hp.measurable.aemeasurable
      (cavitySplitPartition_measurable n d m M f v).log.aestronglyMeasurable).symm
  unfold cavityBulkFullLog
  have he : (fun p : BulkDisorder (m+1) M×EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)=>
      Real.log (cavityBulkFullCompPartition n d m M f v p))=
      (fun p=>Real.log (cavitySplitPartition n d m M f v (Prod.map id (cavityBulkNoiseSplit n d m M) p))) := by
    funext p
    exact congrArg Real.log (cavitySplitPartition_identity n d m M f v p.1 p.2)
  rw [he,h,integral_prod _ (cavitySplitLog_integrable n d m M f hf v)]
  apply integral_congr_ae
  filter_upwards [(cavitySplitLog_integrable n d m M f hf v).prod_right_ae] with a ha
  exact integral_prod_symm _ ha

end SphericalPerceptronFreeEnergy
end

end OAI
