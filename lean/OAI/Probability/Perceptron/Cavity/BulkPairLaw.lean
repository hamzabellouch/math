import Mathlib
import OAI.Probability.Perceptron.Variational.MarkedVariance
import OAI.Probability.Perceptron.Cavity.BulkEmpiricalLimit

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

abbrev BulkPairRange (K : ℝ) := CompactOverlap × Icc (-K) K

def bulkFiniteReplicaLaw (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    Measure (BulkDisorder (n+1) M × (Fin r→NormalizedSpin (n+1))) := by
  letI := gibbsProbabilityKernel_markov (bulkSpinKernel n M)
    (fun a => bulkHamiltonian (n+1) M f v a.1 a.2) (bulkHamiltonian_continuous _ _ _ _).measurable
  exact (bulkDisorderLaw (n+1) M) ⊗ₘ kernelReplica
    (gibbsProbabilityKernel (bulkSpinKernel n M)
      (fun a => bulkHamiltonian (n+1) M f v a.1 a.2)) r

instance bulkFiniteReplicaLaw_probability (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    IsProbabilityMeasure (bulkFiniteReplicaLaw n M r f v) := by
  let := gibbsProbabilityKernel_markov (bulkSpinKernel n M)
    (fun a => bulkHamiltonian (n+1) M f v a.1 a.2) (bulkHamiltonian_continuous _ _ _ _).measurable
  unfold bulkFiniteReplicaLaw
  infer_instance

lemma bulkFiniteReplicaLaw_integral (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (G : BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hG : Measurable (Function.uncurry G)) {C : ℝ} (hb : ∀ a x,|G a x|≤C) :
    (∫ p,G p.1 p.2 ∂bulkFiniteReplicaLaw n M r f v)=bulkReplicaMean n M f v r G := by
  have hi : Integrable (Function.uncurry G) (bulkFiniteReplicaLaw n M r f v) :=
    Integrable.of_bound hG.aestronglyMeasurable C (ae_of_all _ fun p => by
      simpa only [Real.norm_eq_abs, Function.uncurry] using hb p.1 p.2)
  change (∫ p,Function.uncurry G p ∂bulkFiniteReplicaLaw n M r f v)=_
  rw [bulkFiniteReplicaLaw,Measure.integral_compProd hi]
  apply integral_congr_ae
  exact ae_of_all _ fun a => gibbsProbabilityKernel_replica_integral (bulkSpinKernel n M)
    (fun a => bulkHamiltonian (n+1) M f v a.1 a.2) (bulkHamiltonian_continuous _ _ _ _).measurable
    a (bulkHamiltonian_exp_integrable n M f v a) r (G a)

def bulkCompactPair (n M : ℕ) (w : ℝ→ᵇℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖w‖^2≤K)
    (p : BulkDisorder (n+1) M × (Fin 2→NormalizedSpin (n+1))) : BulkPairRange K :=
  (bulkOverlap (p.2 1) (p.2 0),⟨bulkPairAverage n M w p.1 p.2,
    abs_le.mp ((bulkPairAverage_bound n M w p.1 p.2).trans hK)⟩)

lemma bulkCompactPair_measurable (n M : ℕ) (w : ℝ→ᵇℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖w‖^2≤K) : Measurable (bulkCompactPair n M w K hK) := by
  have hp : Measurable (fun p : BulkDisorder (n+1) M × (Fin 2→NormalizedSpin (n+1)) =>
      (p.2 1,p.2 0)) :=
    ((measurable_pi_apply 1).comp measurable_snd).prodMk
      ((measurable_pi_apply 0).comp measurable_snd)
  exact ((bulkOverlap_measurable (n+1)).comp hp).prodMk
    (bulkPairAverage_measurable n M w |>.subtype_mk)

def bulkPairLaw (n M : ℕ) (f w : ℝ→ᵇℝ) (v : ℕ→ℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖w‖^2≤K) : ProbabilityMeasure (BulkPairRange K) :=
  ⟨(bulkFiniteReplicaLaw n M 2 f v).map (bulkCompactPair n M w K hK),
    inferInstance⟩

lemma bulkPairLaw_integral (n M : ℕ) (f w : ℝ→ᵇℝ) (v : ℕ→ℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖w‖^2≤K) (F : BulkPairRange K→ᵇℝ) :
    (∫ p,F p ∂(bulkPairLaw n M f w v K hK : Measure (BulkPairRange K)))=
      bulkReplicaMean n M f v 2 (fun a x => F (bulkCompactPair n M w K hK (a,x))) := by
  change (∫ p,F p ∂(bulkFiniteReplicaLaw n M 2 f v).map (bulkCompactPair n M w K hK))=_
  have he := integral_map (μ:=bulkFiniteReplicaLaw n M 2 f v)
    (bulkCompactPair_measurable n M w K hK).aemeasurable F.measurable.aestronglyMeasurable
  change (∫ p,F p ∂(bulkFiniteReplicaLaw n M 2 f v).map (bulkCompactPair n M w K hK))=
    (∫ p,F (bulkCompactPair n M w K hK p) ∂bulkFiniteReplicaLaw n M 2 f v) at he
  rw [he]
  exact bulkFiniteReplicaLaw_integral n M 2 f v
    (fun a x => F (bulkCompactPair n M w K hK (a,x)))
    (F.measurable.comp (bulkCompactPair_measurable n M w K hK))
    (fun a x => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm (bulkCompactPair n M w K hK (a,x)))

lemma bulkPairLaw_overlap (n M : ℕ) (f w : ℝ→ᵇℝ) (v : ℕ→ℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖w‖^2≤K) (F : CompactOverlap→ᵇℝ) :
    (∫ p,F p.1 ∂(bulkPairLaw n M f w v K hK : Measure (BulkPairRange K)))=
      ∫ Q : CompactArray CompactOverlap,F (Q 0 1) ∂(bulkGibbsArrayLaw n M f v : Measure _) := by
  let A : BulkPairRange K→ᵇℝ := F.compContinuous ⟨Prod.fst,continuous_fst⟩
  rw [show (∫ p,F p.1 ∂(bulkPairLaw n M f w v K hK : Measure (BulkPairRange K)))=(∫ p,A p ∂(bulkPairLaw n M f w v K hK : Measure (BulkPairRange K))) from rfl,
    bulkPairLaw_integral]
  let G : CompactBlock CompactOverlap 2→ᵇℝ := F.compContinuous ⟨fun Q=>Q 0 1,by fun_prop⟩
  have he := bulkGibbsArray_block n M f v 2 G
  change (∫ Q : CompactArray CompactOverlap,F (Q 0 1) ∂(bulkGibbsArrayLaw n M f v : Measure _))=_ at he
  rw [he]
  unfold bulkReplicaMean
  apply integral_congr_ae
  exact ae_of_all _ fun a => by
    apply congrArg (gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) 2)
    funext x
    change F (bulkOverlap (x 1) (x 0))=F (bulkOverlap (x 0) (x 1))
    congr 1
    apply Subtype.ext
    exact real_inner_comm _ _

lemma compact_pair_zero_variance (K : ℝ) (hK : 0≤K)
    (μ : ProbabilityMeasure (BulkPairRange K)) (ν : ProbabilityMeasure CompactOverlap)
    (a : ℝ→ℝ) (ha : Measurable a) (A : ℝ) (hA : 0≤A) (hb : ∀ r,|a r|≤A)
    (hmarg : (μ : Measure (BulkPairRange K)).map Prod.fst=(ν : Measure CompactOverlap))
    (hfirst : ∀ F : CompactOverlap→ᵇℝ,(∫ p,F p.1*p.2.val ∂(μ : Measure (BulkPairRange K)))=
      ∫ q,F q*a q.val ∂(ν : Measure CompactOverlap))
    (hsecond : (∫ p,p.2.val^2 ∂(μ : Measure (BulkPairRange K)))=(∫ q,(a q.val)^2 ∂(ν : Measure CompactOverlap))) :
    ∀ᵐ p ∂(μ : Measure (BulkPairRange K)),p.2.val=a p.1.val := by
  have hi (G : CompactOverlap→ℝ) (hG : Measurable G) :
      (∫ q,G q ∂(ν : Measure CompactOverlap))=(∫ p,G p.1 ∂(μ : Measure (BulkPairRange K))) := by
    rw [←hmarg]
    exact integral_map measurable_fst.aemeasurable hG.aestronglyMeasurable
  apply marked_zero_variance (μ : Measure (BulkPairRange K)) Prod.fst measurable_fst (fun p => p.2.val)
    (by fun_prop) (fun q => a q.val) (ha.comp measurable_subtype_coe) hA hK
    (fun r => hb r.val) (fun p => abs_le.mpr p.2.prop)
  · intro F
    rw [hfirst F]
    exact hi (fun q => F q*a q.val) (F.measurable.mul (ha.comp measurable_subtype_coe))
  · rw [hsecond]
    exact hi (fun q => (a q.val)^2) ((ha.comp measurable_subtype_coe).pow_const 2)


def compactPairMarginal (ν : ProbabilityMeasure (CompactArray CompactOverlap)) :
    ProbabilityMeasure CompactOverlap :=
  ν.map (fun Q : CompactArray CompactOverlap => Q 0 1)

lemma compactPairMarginal_integral (ν : ProbabilityMeasure (CompactArray CompactOverlap))
    (F : CompactOverlap→ℝ) (hF : Measurable F) :
    (∫ r,F r ∂(compactPairMarginal ν : Measure CompactOverlap))=
      ∫ Q : CompactArray CompactOverlap,F (Q 0 1) ∂(ν : Measure _) :=
  integral_map (by exact (by fun_prop : Measurable (fun Q : CompactArray CompactOverlap => Q 0 1)).aemeasurable) hF.aestronglyMeasurable

lemma bulkPairLaw_limit_marginal (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    (w : ℝ→ᵇℝ) (K : ℝ)
    (hK : ∀ n,((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)*‖w‖^2≤K)
    (ν : ProbabilityMeasure (CompactArray CompactOverlap)) (μ : ProbabilityMeasure (BulkPairRange K))
    (hpair : Tendsto (fun n => bulkPairLaw (s n) (M (s n)+2) g.f w (v (s n)) K (hK n)) atTop (𝓝 μ))
    (hover : ∀ F : CompactOverlap→ᵇℝ,
      Tendsto (fun n => ∫ Q : CompactArray CompactOverlap,F (Q 0 1)
        ∂(bulkGibbsArrayLaw (s n) (M (s n)+2) g.f (v (s n)) : Measure _)) atTop
        (𝓝 (∫ Q : CompactArray CompactOverlap,F (Q 0 1) ∂(ν : Measure _)))) :
    (μ : Measure (BulkPairRange K)).map Prod.fst=(compactPairMarginal ν : Measure CompactOverlap) := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  let A : BulkPairRange K→ᵇℝ := F.compContinuous ⟨Prod.fst,continuous_fst⟩
  have he := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction A).continuousAt.tendsto.comp hpair
  change Tendsto (fun n => ∫ p,F p.1 ∂(bulkPairLaw (s n) (M (s n)+2) g.f w (v (s n)) K (hK n) : Measure (BulkPairRange K)))
    atTop (𝓝 (∫ p,F p.1 ∂(μ : Measure (BulkPairRange K)))) at he
  simp_rw [bulkPairLaw_overlap] at he
  have hi := integral_map (μ:=(μ : Measure (BulkPairRange K))) measurable_fst.aemeasurable F.measurable.aestronglyMeasurable
  change (∫ r,F r ∂(μ : Measure (BulkPairRange K)).map Prod.fst)=(∫ p,F p.1 ∂(μ : Measure (BulkPairRange K))) at hi
  rw [hi,compactPairMarginal_integral ν F F.measurable]
  exact tendsto_nhds_unique he (hover F)

theorem bulkPairLaw_identification (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    (hs : Tendsto s atTop atTop) (α : ℝ) (hα : 0≤α)
    (hd : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    (ν : ProbabilityMeasure (CompactArray CompactOverlap))
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect (bulkJointLaw ν) r i G a=0)
    (hgeo : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val)
    (w : ℝ→ᵇℝ) (K : ℝ) (hK0 : 0≤K)
    (hK : ∀ n,((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)*‖w‖^2≤K)
    (μ : ProbabilityMeasure (BulkPairRange K))
    (hpair : Tendsto (fun n => bulkPairLaw (s n) (M (s n)+2) g.f w (v (s n)) K (hK n)) atTop (𝓝 μ)) :
    ∃ a : ℝ→ℝ, Monotone a ∧ (∀ r,0≤a r ∧ a r≤α*‖w‖^2) ∧
      (μ : Measure (BulkPairRange K)).map Prod.fst=(compactPairMarginal ν : Measure CompactOverlap) ∧
      ∀ᵐ p ∂(μ : Measure (BulkPairRange K)),p.2.val=a p.1.val := by
  obtain ⟨a,ham,hab,ht⟩ := bulk_marked_empirical_limits M g v s hs α hd hlim hGG hgeo hn w
  have hmarg := bulkPairLaw_limit_marginal M g v s w K hK ν μ hpair
    (bulk_full_pair_tendsto M g v s hlim hGG hgeo hn)
  have htμ (F : C(BulkPairRange K,ℝ)) :
      Tendsto (fun n => ∫ p,F p ∂(bulkPairLaw (s n) (M (s n)+2) g.f w (v (s n)) K (hK n) : Measure (BulkPairRange K)))
        atTop (𝓝 (∫ p,F p ∂(μ : Measure (BulkPairRange K)))) :=
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction (BoundedContinuousFunction.mkOfCompact F)).continuousAt.tendsto.comp hpair
  refine ⟨fun r => α*a r,ham.const_mul hα,fun r =>
    ⟨mul_nonneg hα (hab r).1,mul_le_mul_of_nonneg_left (hab r).2 hα⟩,hmarg,?_⟩
  apply compact_pair_zero_variance K hK0 μ (compactPairMarginal ν) (fun r => α*a r)
    (ham.measurable.const_mul α) (α*‖w‖^2) (mul_nonneg hα (sq_nonneg _))
    (fun r => by rw [abs_of_nonneg (mul_nonneg hα (hab r).1)]; exact mul_le_mul_of_nonneg_left (hab r).2 hα) hmarg
  · intro F
    let A : C(BulkPairRange K,ℝ) := ⟨fun p => F p.1*p.2.val,by fun_prop⟩
    have he := htμ A
    have htest n : (∫ p,A p ∂(bulkPairLaw (s n) (M (s n)+2) g.f w (v (s n)) K (hK n) : Measure (BulkPairRange K)))=
        bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 2
          (fun d x => bulkPairOverlapTest (s n) F x*bulkPairAverage (s n) (M (s n)+2) w d x) :=
      bulkPairLaw_integral _ _ _ _ _ _ _ (BoundedContinuousFunction.mkOfCompact A)
    simp_rw [htest] at he
    have hvalue := tendsto_nhds_unique he (ht F).1
    change (∫ p,A p ∂(μ : Measure (BulkPairRange K)))=_
    rw [hvalue,compactPairMarginal_integral ν (fun q => F q*(α*a q.val)) (F.measurable.mul (ham.measurable.comp measurable_subtype_coe |>.const_mul α)),←integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun Q => by ring
  · let A : C(BulkPairRange K,ℝ) := ⟨fun p => p.2.val^2,by fun_prop⟩
    have he := htμ A
    have htest n : (∫ p,A p ∂(bulkPairLaw (s n) (M (s n)+2) g.f w (v (s n)) K (hK n) : Measure (BulkPairRange K)))=
        bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 2
          (fun d x => bulkPairOverlapTest (s n) 1 x*(bulkPairAverage (s n) (M (s n)+2) w d x)^2) := by
      have hi := bulkPairLaw_integral (s n) (M (s n)+2) g.f w (v (s n)) K (hK n) (BoundedContinuousFunction.mkOfCompact A)
      change (∫ p,A p ∂(bulkPairLaw (s n) (M (s n)+2) g.f w (v (s n)) K (hK n) : Measure (BulkPairRange K)))=
        bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 2
          (fun d x => (bulkPairAverage (s n) (M (s n)+2) w d x)^2) at hi
      simpa only [bulkPairOverlapTest,BoundedContinuousFunction.coe_one,Pi.one_apply,one_mul] using hi
    simp_rw [htest] at he
    have hvalue := tendsto_nhds_unique he (ht 1).2
    change (∫ p,A p ∂(μ : Measure (BulkPairRange K)))=_
    rw [hvalue,compactPairMarginal_integral ν (fun q => (α*a q.val)^2) ((ham.measurable.comp measurable_subtype_coe |>.const_mul α).pow_const 2),←integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun Q => by simp; ring

end SphericalPerceptronFreeEnergy
end

end OAI
