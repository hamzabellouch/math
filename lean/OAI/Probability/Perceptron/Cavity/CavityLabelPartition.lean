import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityLabelMoment
import OAI.Probability.Perceptron.Cascade.CavityCappedRPC

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

instance cavityIndexMeasurableSingleton (n d : ℕ) : MeasurableSingletonClass (Fin (n+1)⊕Fin d) where
  measurableSet_singleton x := by
    cases x with
    | inl x => simpa only [Set.image_singleton] using (measurableSet_singleton x).inl_image (β:=Fin d)
    | inr x => simpa only [Set.image_singleton] using (measurableSet_singleton x).inr_image (α:=Fin (n+1))

def cavityLabelPartition (n d k : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ)
    (p : IndexedCascadeBase k×(ℕ→ℝ)) : ℝ :=
  ∫ l,cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ)
    (cavityCountableField (cavityLabelRow q) (cavityLabelLength k) p.2 l)
    ∂indexedLeafProbability k p.1

lemma cavityLabelPartition_measurable (n d k : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ) :
    Measurable (cavityLabelPartition n d k f Λ hΛ σ q) := by
  let κ : Kernel (IndexedCascadeBase k×(ℕ→ℝ)) (IndexedLeaf k):=
    (indexedLeafKernel k).comap Prod.fst measurable_fst
  have hf : Measurable (fun p : (ℕ→ℝ)×IndexedLeaf k=>
      cavityCountableField (cavityLabelRow q) (cavityLabelLength k) p.1 p.2) :=
    cavityCountableField_measurable (cavityLabelRow q) (cavityLabelLength k)
      (cavityLabelRow_measurable q) (cavityLabelLength_measurable k)
  have hp : Measurable (fun p : (IndexedCascadeBase k×(ℕ→ℝ))×IndexedLeaf k=>(p.1.2,p.2)) :=
    measurable_fst.snd.prodMk measurable_snd
  have hg:=hf.comp hp
  have hm : Measurable (fun p : (IndexedCascadeBase k×(ℕ→ℝ))×IndexedLeaf k=>
      cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ)
        (cavityCountableField (cavityLabelRow q) (cavityLabelLength k) p.1.2 p.2)) :=
    (cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ)).measurable.comp hg
  exact (hm.stronglyMeasurable.integral_kernel_prod_right (κ:=κ)
    (f:=fun p l=>cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ)
      (cavityCountableField (cavityLabelRow q) (cavityLabelLength k) p.2 l))).measurable

lemma cavityLabelPartition_mem (n d k : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ)
    (p : IndexedCascadeBase k×(ℕ→ℝ)) :
    cavityLabelPartition n d k f Λ hΛ σ q p∈CavityPartitionRange d f Λ := by
  let Ψ:=cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ)
  have hm : Measurable (fun l=>Ψ (cavityCountableField (cavityLabelRow q) (cavityLabelLength k) p.2 l)) :=
    measurable_of_countable _
  have hi : Integrable (fun l=>Ψ (cavityCountableField (cavityLabelRow q) (cavityLabelLength k) p.2 l))
      (indexedLeafProbability k p.1) :=
    Integrable.of_bound hm.aestronglyMeasurable ‖Ψ‖ (ae_of_all _ fun l=>Ψ.norm_coe_le_norm _)
  unfold cavityLabelPartition
  constructor
  · simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono (integrable_const (Real.exp (-(d:ℝ)*‖f‖))) hi
        (fun l=>(cavityResidualCapped_bounds n d f Λ hΛ σ _).1)
  · simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono hi (integrable_const (Λ*Real.exp ((d:ℝ)*‖f‖)))
        (fun l=>(cavityResidualCapped_bounds n d f Λ hΛ σ _).2)

def cavityLabelPartitionLaw (n d k : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ) (z : Fin k→ℝ) :
    ProbabilityMeasure (CavityPartitionRange d f Λ) :=
  ⟨((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod countableGaussianLaw).map
    (fun p=>⟨cavityLabelPartition n d k f Λ hΛ σ q p,cavityLabelPartition_mem n d k f Λ hΛ σ q p⟩),
    inferInstance⟩

lemma cavityLabelPartitionLaw_integral (n d k : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ) (z : Fin k→ℝ)
    (F : ℝ→ℝ) (hF : Measurable F) :
    (∫ x,F x.val ∂(cavityLabelPartitionLaw n d k f Λ hΛ σ q z : Measure (CavityPartitionRange d f Λ)))=
      ∫ p,F (cavityLabelPartition n d k f Λ hΛ σ q p)
        ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod countableGaussianLaw := by
  exact integral_map ((cavityLabelPartition_measurable n d k f Λ hΛ σ q).subtype_mk).aemeasurable
    (hF.comp measurable_subtype_coe).aestronglyMeasurable

theorem cavityLabelPartitionLaw_moment (n d k : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ)
    (h0 : ∀ i,0≤q 0 i) (hq : ∀ i,Monotone (fun l=>q l i))
    (D : Fin (n+1)⊕Fin d→ℝ) (hD : ∀ i,q (Fin.last k) i≤D i) (z : Fin k→ℝ) (r : ℕ) :
    (∫ x,x.val^r ∂(cavityLabelPartitionLaw n d k f Λ hΛ
      (fun j=>Real.sqrt (D j-q (Fin.last k) j)) q z : Measure (CavityPartitionRange d f Λ)))=
    ∫ b,∫ xs : Fin r→IndexedLeaf k,cavityMatrixKernel (cavityTestReplica (cavitySingleTest n d f Λ hΛ) r)
      (fun p t : (Fin (n+1)⊕Fin d)×Fin r=>if p=t then D p.1 else
        if p.1=t.1 then q (indexedCommonDepth k (xs t.2) (xs p.2)) p.1 else 0)
      ∂Measure.pi (fun _=>indexedLeafProbability k b) ∂indexedCascadeBaseLaw k z := by
  let σ:=fun j=>Real.sqrt (D j-q (Fin.last k) j)
  let P:=cavityLabelPartition n d k f Λ hΛ σ q
  have hb (p : IndexedCascadeBase k×(ℕ→ℝ)) : ‖P p‖≤Λ*Real.exp ((d:ℝ)*‖f‖) := by
    have hh:=cavityLabelPartition_mem n d k f Λ hΛ σ q p
    rw [Real.norm_eq_abs,abs_of_pos ((Real.exp_pos _).trans_le hh.1)]
    exact hh.2
  have hi : Integrable (fun p=>P p^r) ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod countableGaussianLaw) :=
    Integrable.of_bound ((cavityLabelPartition_measurable n d k f Λ hΛ σ q).pow_const r).aestronglyMeasurable
      ((Λ*Real.exp ((d:ℝ)*‖f‖))^r) (ae_of_all _ fun p=>by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hb p) r)
  rw [cavityLabelPartitionLaw_integral _ _ _ _ _ _ _ _ _ (fun x : ℝ=>x^r) (by fun_prop),integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ fun b=>cavity_label_true_diagonal_moment q h0 hq D hD
    (indexedLeafProbability k b) (cavitySingleTest n d f Λ hΛ) r


def cavityIndexedRootPartition (n d k : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ)
    (p : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)×
      (IndexedCascadeBase k×IndexedCascadeMarks (EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) k)) : ℝ :=
  ∫ l,cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ)
    (indexedLeafState (gaussianLinearMarkStep (fun j=>diagonalMark (profileGaussianStep q j))) k
      ((fun _=>diagonalMark (profileGaussianRoot q) p.1),p.2.2) l 0)
    ∂indexedLeafProbability k p.2.1

lemma cavityIndexedRootPartition_measurable (n d k : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ) :
    Measurable (cavityIndexedRootPartition n d k f Λ hΛ σ q) := by
  let E:=EuclideanSpace ℝ (Fin (n+1)⊕Fin d)
  let X:=E×(IndexedCascadeBase k×IndexedCascadeMarks E k)
  let κ : Kernel X (IndexedLeaf k):=(indexedLeafKernel k).comap (fun p=>p.2.1) measurable_snd.fst
  have hm0 : Measurable (fun p : X×IndexedLeaf k=>
      indexedLeafState (gaussianLinearMarkStep (fun j=>diagonalMark (profileGaussianStep q j))) k
        ((fun _=>diagonalMark (profileGaussianRoot q) p.1.1),p.1.2.2) p.2) := by
    have hs := indexedLeafState_measurable
      (gaussianLinearMarkStep_measurable (fun j=>diagonalMark (profileGaussianStep q j))) k
    have hp : Measurable (fun p : X×IndexedLeaf k=>
        (((fun _ : ℕ=>diagonalMark (profileGaussianRoot q) p.1.1),p.1.2.2),p.2)) := by
      have hr : Measurable (fun p : X×IndexedLeaf k=>
          (fun _ : ℕ=>diagonalMark (profileGaussianRoot q) p.1.1)) :=
        Measurable.of_eval fun _=>
          (diagonalMark (profileGaussianRoot q)).measurable.comp measurable_fst.fst
      exact (hr.prodMk measurable_fst.snd.snd).prodMk measurable_snd
    exact hs.comp hp
  have hm : Measurable (fun p : X×IndexedLeaf k=>
      cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ)
        (indexedLeafState (gaussianLinearMarkStep (fun j=>diagonalMark (profileGaussianStep q j))) k
          ((fun _=>diagonalMark (profileGaussianRoot q) p.1.1),p.1.2.2) p.2 0)) :=
    (cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ)).measurable.comp
      ((measurable_pi_apply 0).comp hm0)
  exact (hm.stronglyMeasurable.integral_kernel_prod_right (κ:=κ)
    (f:=fun p l=>cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ)
      (indexedLeafState (gaussianLinearMarkStep (fun j=>diagonalMark (profileGaussianStep q j))) k
        ((fun _=>diagonalMark (profileGaussianRoot q) p.1),p.2.2) l 0))).measurable

lemma cavityIndexedRootPartition_log_bound (n d k : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ)
    (p : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)×
      (IndexedCascadeBase k×IndexedCascadeMarks (EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) k)) :
    |Real.log (cavityIndexedRootPartition n d k f Λ hΛ σ q p)|≤Real.log Λ+d*‖f‖ := by
  let V : IndexedLeaf k→_:=fun l=>indexedLeafState
    (gaussianLinearMarkStep (fun j=>diagonalMark (profileGaussianStep q j))) k
      ((fun _=>diagonalMark (profileGaussianRoot q) p.1),p.2.2) l 0
  have hh:=tilt_log_partition_bound (indexedLeafProbability k p.2.1)
    (H:=fun l=>Real.log (cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ) (V l)))
    (measurable_of_countable _) (add_nonneg (Real.log_nonneg hΛ) (by positivity))
    (fun l=>cavityResidualCapped_log_bound n d f Λ hΛ σ (V l))
  simpa only [tiltPartition,one_mul,Real.exp_log (cavityResidualCapped_pos n d f Λ hΛ σ _),
    cavityIndexedRootPartition,V] using hh

lemma cavityIndexedRoot_disorder_preserving (k : ℕ) (J : Type) [Fintype J] (z : Fin k→ℝ) :
    MeasurePreserving
      (fun p : IndexedCascadeBase k×(ℕ→ℝ)=>
        ((indexedGaussianDisorder k J p.2).1,(p.1,(indexedGaussianDisorder k J p.2).2)))
      ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod countableGaussianLaw)
      ((stdGaussian (EuclideanSpace ℝ J)).prod
        ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
          (indexedCascadeMarksLaw (gaussianMarkLaw (E:=EuclideanSpace ℝ J)) k))) := by
  have hg : MeasurePreserving (indexedGaussianDisorder k J) countableGaussianLaw
      ((stdGaussian (EuclideanSpace ℝ J)).prod
        (indexedCascadeMarksLaw (gaussianMarkLaw (E:=EuclideanSpace ℝ J)) k)) :=
    ⟨indexedGaussianDisorder_measurable k J,indexedGaussianDisorder_law k J⟩
  exact (freshRoot_swap_nested _ _ _).comp ((MeasurePreserving.id _).prod hg)

theorem cavityLabelPartitionLaw_log_recursion (n d k : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ)
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1) :
    (∫ x,Real.log x.val ∂(cavityLabelPartitionLaw n d k f Λ hΛ σ q z : Measure (CavityPartitionRange d f Λ)))=
    ∫ y,finiteCascadeLogRecursion (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))
      (gaussianLinearMarkStep (fun j=>diagonalMark (profileGaussianStep q j))) k z
      (fun s=>Real.log (cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ) (s 0)))
      (fun _=>diagonalMark (profileGaussianRoot q) y) ∂stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) := by
  let F:=fun p=>Real.log (cavityIndexedRootPartition n d k f Λ hΛ σ q p)
  have hm : Measurable F := (cavityIndexedRootPartition_measurable n d k f Λ hΛ σ q).log
  have hp:=cavityIndexedRoot_disorder_preserving k (Fin (n+1)⊕Fin d) z
  have hi : Integrable F ((stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d))).prod
      ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        (indexedCascadeMarksLaw (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin (n+1)⊕Fin d))) k))) :=
    Integrable.of_bound hm.aestronglyMeasurable (Real.log Λ+d*‖f‖) (ae_of_all _ fun p=>by
      simpa only [Real.norm_eq_abs] using cavityIndexedRootPartition_log_bound n d k f Λ hΛ σ q p)
  rw [cavityLabelPartitionLaw_integral _ _ _ _ _ _ _ _ _ Real.log Real.measurable_log]
  have he (p : IndexedCascadeBase k×(ℕ→ℝ)) :
      Real.log (cavityLabelPartition n d k f Λ hΛ σ q p)=
        F ((indexedGaussianDisorder k (Fin (n+1)⊕Fin d) p.2).1,
          (p.1,(indexedGaussianDisorder k (Fin (n+1)⊕Fin d) p.2).2)) := by
    unfold cavityLabelPartition F cavityIndexedRootPartition
    simp_rw [cavity_label_field_state]
  simp_rw [he]
  rw [←integral_map hp.measurable.aemeasurable hm.aestronglyMeasurable,hp.map_eq,integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ fun y=>cavity_capped_indexed_log_recursion n d k f Λ hΛ σ
    (fun j=>diagonalMark (profileGaussianStep q j)) z hz hz0 hz1
    (fun _=>diagonalMark (profileGaussianRoot q) y)

end SphericalPerceptronFreeEnergy
end

end OAI
