import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityLabelPartition

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

 def cavityLabelMarkedArray {K : ℝ} {k : ℕ} (p : Fin (k+1)→BulkPairRange K)
    (D : BulkPairRange K) (xs : ℕ→IndexedLeaf k) : CompactArray (BulkPairRange K) :=
  fun i j=>if i=j then D else p (indexedCommonDepth k (xs j) (xs i))

lemma cavityLabelMarkedArray_measurable {K : ℝ} {k : ℕ} (p : Fin (k+1)→BulkPairRange K)
    (D : BulkPairRange K) : Measurable (cavityLabelMarkedArray p D) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  unfold cavityLabelMarkedArray
  split_ifs
  · exact measurable_const
  · have hf : Measurable (fun x : IndexedLeaf k×IndexedLeaf k=>p (indexedCommonDepth k x.1 x.2)) :=
      measurable_of_countable _
    have hg : Measurable (fun xs : ℕ→IndexedLeaf k=>(xs j,xs i)) :=
      (measurable_pi_apply j).prodMk (measurable_pi_apply i)
    exact hf.comp hg

lemma cavityLabelZero_measurable (k : ℕ) :
    Measurable (Function.uncurry (fun _ : IndexedCascadeBase k=>fun _ : IndexedLeaf k=>(0:ℝ))) :=
  measurable_const

def cavityLabelMarkedLaw {K : ℝ} {k : ℕ} (p : Fin (k+1)→BulkPairRange K)
    (D : BulkPairRange K) (z : Fin k→ℝ) : ProbabilityMeasure (CompactArray (BulkPairRange K)) := by
  let μ : Measure (IndexedCascadeBase k×(ℕ→IndexedLeaf k)) :=
    annealedInfiniteReplicaMeasure (indexedLeafKernel k)
      (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)) (fun _ _=>0) (cavityLabelZero_measurable k)
  have : IsProbabilityMeasure μ := by
    have : IsMarkovKernel (gibbsProbabilityKernel (indexedLeafKernel k) (fun _ _=>0)) :=
      gibbsProbabilityKernel_markov (indexedLeafKernel k) (fun _ _=>0) (cavityLabelZero_measurable k)
    dsimp [μ]
    unfold annealedInfiniteReplicaMeasure
    infer_instance
  have hm : Measurable (fun a : IndexedCascadeBase k×(ℕ→IndexedLeaf k)=>cavityLabelMarkedArray p D a.2) :=
    (cavityLabelMarkedArray_measurable p D).comp measurable_snd
  exact ⟨μ.map (fun a=>cavityLabelMarkedArray p D a.2),
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance⟩

lemma cavityLabelMarkedLaw_block {K : ℝ} {k : ℕ} (p : Fin (k+1)→BulkPairRange K)
    (D : BulkPairRange K) (z : Fin k→ℝ) (r : ℕ) (F : CompactBlock (BulkPairRange K) r→ᵇℝ) :
    (∫ Q,F (compactBlock r Q) ∂(cavityLabelMarkedLaw p D z : Measure (CompactArray (BulkPairRange K))))=
      ∫ b,∫ xs : Fin r→IndexedLeaf k,F (fun i j=>if i=j then D else
        p (indexedCommonDepth k (xs j) (xs i)))
        ∂Measure.pi (fun _=>indexedLeafProbability k b) ∂indexedCascadeBaseLaw k z := by
  let G : (Fin r→IndexedLeaf k)→ℝ:=fun xs=>F (fun i j=>if i=j then D else
    p (indexedCommonDepth k (xs j) (xs i)))
  have hG : Measurable G:=measurable_of_countable _
  have hGB (xs : Fin r→IndexedLeaf k) : |G xs|≤‖F‖:=F.norm_coe_le_norm _
  have he : ∀ᵐ b ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)),
      Integrable (fun _ : IndexedLeaf k=>Real.exp 0) (indexedLeafKernel k b) :=
    ae_of_all _ fun _=>integrable_const _
  have hh:=annealedInfiniteReplica_gibbs_prefix (indexedLeafKernel k)
    (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)) (fun _ _=>0) (cavityLabelZero_measurable k) he r hG hGB
  change (∫ Q,F (compactBlock r Q) ∂Measure.map
    (fun a : IndexedCascadeBase k×(ℕ→IndexedLeaf k)=>cavityLabelMarkedArray p D a.2)
    (annealedInfiniteReplicaMeasure (indexedLeafKernel k)
      (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)) (fun _ _=>0) (cavityLabelZero_measurable k)))=_
  erw [integral_map
    ((cavityLabelMarkedArray_measurable p D).comp measurable_snd).aemeasurable
    (F.measurable.comp (compactBlock_continuous r).measurable).aestronglyMeasurable]
  have hf : (fun a : IndexedCascadeBase k×(ℕ→IndexedLeaf k)=>F (compactBlock r (cavityLabelMarkedArray p D a.2)))=
      fun a=>G (fun i=>a.2 i.val) := by
    funext a
    apply congrArg F
    funext i j
    simp only [compactBlock,cavityLabelMarkedArray,Fin.val_inj]
  change (∫ a : IndexedCascadeBase k×(ℕ→IndexedLeaf k),
    F (compactBlock r (cavityLabelMarkedArray p D a.2))
    ∂annealedInfiniteReplicaMeasure (indexedLeafKernel k)
      (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)) (fun _ _=>0) (cavityLabelZero_measurable k))=_
  rw [hf,hh]
  apply integral_congr_ae
  exact ae_of_all _ fun b=>by
    simp only [gibbsReplicaMean,tiltMean,tiltIntegral,tiltPartition,replicaPotential,
      Finset.sum_const_zero,mul_zero,Real.exp_zero,one_mul,integral_const,probReal_univ,one_smul,div_one,
      indexedLeafKernel,Kernel.coe_mk]
    rfl

def cavityPairProfile (n d : ℕ) {K : ℝ} {k : ℕ} (p : Fin (k+1)→BulkPairRange K) :
    Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ :=
  fun l=>Sum.elim (fun _=>(p l).2.val) (fun _=>(p l).1.val)

def cavityPairDiagonal (n d : ℕ) {K : ℝ} (D : BulkPairRange K) :
    (Fin (n+1)⊕Fin d)→ℝ := Sum.elim (fun _=>D.2.val) (fun _=>D.1.val)

lemma cavityPair_block_covariance (n d r : ℕ) {K : ℝ} {k : ℕ}
    (p : Fin (k+1)→BulkPairRange K) (D : BulkPairRange K) (xs : Fin r→IndexedLeaf k) :
    (fun i j : CavityReplicaIndex n d r=>if i.1=j.1 then Sum.elim
      (fun _=>(if i.2=j.2 then D else p (indexedCommonDepth k (xs j.2) (xs i.2))).2.val)
      (fun _=>(if i.2=j.2 then D else p (indexedCommonDepth k (xs j.2) (xs i.2))).1.val) i.1 else 0)=
    (fun i j=>if i=j then cavityPairDiagonal n d D i.1 else
      if i.1=j.1 then cavityPairProfile n d p (indexedCommonDepth k (xs j.2) (xs i.2)) i.1 else 0) := by
  funext i j
  by_cases h1 : i.1=j.1
  · by_cases h2 : i.2=j.2
    · have h : i=j:=Prod.ext h1 h2
      simp only [h,ite_true,cavityPairDiagonal]
    · have h : i≠j:=fun hh=>h2 (congrArg Prod.snd hh)
      simp only [h1,h2,h,ite_false,ite_true,cavityPairProfile]
  · have h : i≠j:=fun hh=>h1 (congrArg Prod.fst hh)
    simp only [h1,h,ite_false]

theorem cavityLabelMarkedLaw_cavity_moment (n d : ℕ) {K : ℝ} {k : ℕ}
    (p : Fin (k+1)→BulkPairRange K) (D : BulkPairRange K) (z : Fin k→ℝ)
    (hp0 : ∀ i,0≤cavityPairProfile n d p 0 i)
    (hpm : ∀ i,Monotone (fun l=>cavityPairProfile n d p l i))
    (hpD : ∀ i,cavityPairProfile n d p (Fin.last k) i≤cavityPairDiagonal n d D i)
    (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ) (r : ℕ) :
    (∫ x,x.val^r ∂(cavityLabelPartitionLaw n d k f Λ hΛ
      (fun i=>Real.sqrt (cavityPairDiagonal n d D i-cavityPairProfile n d p (Fin.last k) i))
      (cavityPairProfile n d p) z : Measure (CavityPartitionRange d f Λ)))=
    ∫ Q,cavityArrayKernel n d r f Λ hΛ K Q ∂cavityLabelMarkedLaw p D z := by
  rw [cavityLabelPartitionLaw_moment n d k f Λ hΛ _ hp0 hpm _ hpD z r]
  let F : CompactBlock (BulkPairRange K) r→ᵇℝ :=
    (cavityMatrixKernel (cavityReplicaTest n d r f Λ hΛ)).compContinuous
      ⟨fun Q=>fun i j : CavityReplicaIndex n d r=>if i.1=j.1 then
        Sum.elim (fun _=>(Q i.2 j.2).2.val) (fun _=>(Q i.2 j.2).1.val) i.1 else 0,by
          apply continuous_pi
          intro i
          apply continuous_pi
          intro j
          split_ifs
          · cases i.1 <;> dsimp only [Sum.elim] <;> fun_prop
          · exact continuous_const⟩
  change _=∫ Q,F (compactBlock r Q) ∂cavityLabelMarkedLaw p D z
  rw [cavityLabelMarkedLaw_block]
  apply integral_congr_ae
  exact ae_of_all _ fun b=>integral_congr_ae (ae_of_all _ fun xs=>by
    change _=cavityMatrixKernel (cavityReplicaTest n d r f Λ hΛ) _
    rw [cavitySingleTest_replica]
    apply congrArg (cavityMatrixKernel (cavityReplicaTest n d r f Λ hΛ))
    exact (cavityPair_block_covariance n d r p D xs).symm)

end SphericalPerceptronFreeEnergy
end

end OAI
