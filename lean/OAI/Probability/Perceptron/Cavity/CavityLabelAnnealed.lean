import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityResidualUncap
import OAI.Probability.Perceptron.Variational.KernelProductIntegral

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def cavityLabelFullPartition (n d k : ℕ) (f : ℝ→ᵇℝ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ)
    (p : IndexedCascadeBase k×(ℕ→ℝ)) : ℝ :=
  ∫ x,Real.exp (cavityLabelWeight n d k f σ q (p.2,x))*cavityLabelSpherical n d k σ q (p.2,x)
    ∂(indexedLeafProbability k p.1).prod (stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))

lemma cavityLabelFullPartition_measurable (n d k : ℕ) (f : ℝ→ᵇℝ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ) :
    Measurable (cavityLabelFullPartition n d k f σ q) := by
  have hf := (cavityLabelWeight_measurable n d k f σ q).exp.mul
    (cavityLabelSpherical_measurable n d k σ q)
  have hp : Measurable (fun t : (IndexedCascadeBase k×(ℕ→ℝ))×(IndexedLeaf k×EuclideanSpace ℝ (Fin (n+1)⊕Fin d))=>
      (t.1.2,t.2)) := measurable_fst.snd.prodMk measurable_snd
  exact measurable_kernel_product_integral (indexedLeafKernel k)
    (stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d))) Prod.fst measurable_fst
    (fun t=>Real.exp (cavityLabelWeight n d k f σ q (t.1.2,t.2))*
      cavityLabelSpherical n d k σ q (t.1.2,t.2)) (hf.comp hp)

lemma cavityLabelPartition_eq_product (n d k : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ)
    (p : IndexedCascadeBase k×(ℕ→ℝ)) :
    cavityLabelPartition n d k f Λ hΛ σ q p=
      ∫ x,Real.exp (cavityLabelWeight n d k f σ q (p.2,x))*min (cavityLabelSpherical n d k σ q (p.2,x)) Λ
        ∂(indexedLeafProbability k p.1).prod (stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d))) := by
  let Ψ:=cavitySingleTest n d f Λ hΛ
  let G:=fun x : IndexedLeaf k×EuclideanSpace ℝ (Fin (n+1)⊕Fin d)=>
    Ψ (cavityLabelCompletedMark n d k σ q (p.2,x))
  have hm : Measurable G := Ψ.measurable.comp
    ((cavityLabelCompletedMark_measurable n d k σ q).comp (measurable_const.prodMk measurable_id))
  have hi : Integrable G ((indexedLeafProbability k p.1).prod (stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))) :=
    Integrable.of_bound hm.aestronglyMeasurable ‖Ψ‖ (ae_of_all _ fun x=>Ψ.norm_coe_le_norm _)
  have he x : G x=Real.exp (cavityLabelWeight n d k f σ q (p.2,x))*
      min (cavityLabelSpherical n d k σ q (p.2,x)) Λ := by
    simp only [G,Ψ,cavitySingleTest_apply,cavityLabelWeight,cavityLabelSpherical,Real.exp_sum,gaussianSumSplit]
    rw [mul_comm]
  rw [show (fun x=>Real.exp (cavityLabelWeight n d k f σ q (p.2,x))*
    min (cavityLabelSpherical n d k σ q (p.2,x)) Λ)=G from funext fun x=>(he x).symm,
    integral_prod _ hi]
  rfl

lemma integrable_product_of_nonneg_conditional {B G : Type*}
    [MeasurableSpace B] [MeasurableSpace G] (μ : Measure B) (P : Measure G)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (D : B×G→ℝ) (hD : Measurable D) (K : ℝ)
    (hi : ∀ b,Integrable (fun g=>D (b,g)) P)
    (h0 : ∀ b,∀ᵐ g ∂P,0≤D (b,g)) (hK : ∀ b,(∫ g,D (b,g) ∂P)≤K) :
    Integrable D (μ.prod P) ∧ 0≤∫ p,D p ∂μ.prod P ∧ (∫ p,D p ∂μ.prod P)≤K := by
  have hn b : (∫ g,‖D (b,g)‖ ∂P)=∫ g,D (b,g) ∂P := by
    apply integral_congr_ae
    filter_upwards [h0 b] with g hg
    exact Real.norm_of_nonneg hg
  have hI : Integrable D (μ.prod P) := by
    apply (integrable_prod_iff hD.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ hi,?_⟩
    apply Integrable.of_bound (hD.norm.stronglyMeasurable.integral_prod_right).aestronglyMeasurable K
    filter_upwards [] with b
    rw [hn,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg_of_ae (h0 b))]
    exact hK b
  refine ⟨hI,?_,?_⟩
  · rw [integral_prod _ hI]
    exact integral_nonneg fun b=>integral_nonneg_of_ae (h0 b)
  · rw [integral_prod _ hI]
    calc
      _≤∫ _ : B,K ∂μ := integral_mono hI.integral_prod_left (integrable_const K) hK
      _=K := by simp

theorem cavityLabel_uncap_annealed (n d : ℕ) {K : ℝ} {k : ℕ}
    (p : Fin (k+1)→BulkPairRange K) (D : BulkPairRange K)
    (hp0 : ∀ i,0≤cavityPairProfile n d p 0 i)
    (hpm : ∀ i,Monotone (fun l=>cavityPairProfile n d p l i))
    (hpD : ∀ i,cavityPairProfile n d p (Fin.last k) i≤cavityPairDiagonal n d D i)
    (f : ℝ→ᵇℝ) (z : Fin k→ℝ) {Λ : ℝ} (hΛ : 1≤Λ) :
    let σ:=fun i=>Real.sqrt (cavityPairDiagonal n d D i-cavityPairProfile n d p (Fin.last k) i)
    let E:=fun t=>Real.log (cavityLabelFullPartition n d k f σ (cavityPairProfile n d p) t)-
      Real.log (cavityLabelPartition n d k f Λ hΛ σ (cavityPairProfile n d p) t)
    let P:=(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod countableGaussianLaw
    Integrable E P ∧ 0≤∫ t,E t ∂P ∧ (∫ t,E t ∂P)≤
      Real.exp (2*((d:ℝ)*‖f‖))/Λ*Real.exp (2*(n+1:ℕ)*D.2.val) := by
  let σ:=fun i=>Real.sqrt (cavityPairDiagonal n d D i-cavityPairProfile n d p (Fin.last k) i)
  let q:=cavityPairProfile n d p
  let F:=cavityLabelSpherical n d k σ q
  let W:=cavityLabelWeight n d k f σ q
  let E:=fun t=>Real.log (cavityLabelFullPartition n d k f σ q t)-
    Real.log (cavityLabelPartition n d k f Λ hΛ σ q t)
  have hm : Measurable E := (cavityLabelFullPartition_measurable n d k f σ q).log.sub
    (cavityLabelPartition_measurable n d k f Λ hΛ σ q).log
  have he b g : E (b,g)=Real.log (∫ x,Real.exp (W (g,x))*F (g,x)
      ∂(indexedLeafProbability k b).prod (stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d))))-
    Real.log (∫ x,Real.exp (W (g,x))*min (F (g,x)) Λ
      ∂(indexedLeafProbability k b).prod (stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))) := by
    dsimp only [E]
    rw [cavityLabelPartition_eq_product]
    rfl
  have hc b := cavityLabel_cap_error n d p D hp0 hpm hpD f b hΛ
  have hi b : Integrable (fun g=>E (b,g)) countableGaussianLaw := by simpa only [he] using (hc b).1
  have hbound b : (∫ g,E (b,g) ∂countableGaussianLaw)≤
      Real.exp (2*((d:ℝ)*‖f‖))/Λ*Real.exp (2*(n+1:ℕ)*D.2.val) := by simpa only [he] using (hc b).2.2
  have h0 b : ∀ᵐ g ∂countableGaussianLaw,0≤E (b,g) := by
    have hL2 := (cavity_residual_square_integrable (indexedLeafProbability k b) countableGaussianLaw
      (stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d))) F
      (cavityLabelSpherical_measurable n d k σ q) (Real.exp (2*(n+1:ℕ)*D.2.val))
      (fun x=>(cavityLabelSpherical_second n d p D hp0 hpm hpD x).1)
      (fun x=>(cavityLabelSpherical_second n d p D hp0 hpm hpD x).2)).1
    filter_upwards [hL2.prod_right_ae] with g hg
    have hF : MemLp (fun x=>F (g,x)) 2
        ((indexedLeafProbability k b).prod (stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))) :=
      (memLp_two_iff_integrable_sq ((cavityLabelSpherical_measurable n d k σ q).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mpr hg
    rw [he]
    exact (cavity_capped_log_bound _ ((cavityLabelWeight_measurable n d k f σ q).comp
      (measurable_const.prodMk measurable_id)) (fun x=>cavityLabelWeight_bound n d k f σ q (g,x))
      hF (fun x=>cavityLabelSpherical_one n d k σ q (g,x)) hΛ).1
  exact integrable_product_of_nonneg_conditional (indexedCascadeBaseLaw k z) countableGaussianLaw E hm _ hi h0 hbound

lemma cavityLabel_capped_log_integrable (n d k : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (q : Fin (k+1)→(Fin (n+1)⊕Fin d)→ℝ) (z : Fin k→ℝ) :
    Integrable (fun t=>Real.log (cavityLabelPartition n d k f Λ hΛ σ q t))
      ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod countableGaussianLaw) := by
  apply Integrable.of_bound (cavityLabelPartition_measurable n d k f Λ hΛ σ q).log.aestronglyMeasurable
    ‖cavityPartitionLogTest d f Λ‖
  exact ae_of_all _ fun t=>(cavityPartitionLogTest d f Λ).norm_coe_le_norm
    ⟨cavityLabelPartition n d k f Λ hΛ σ q t,cavityLabelPartition_mem n d k f Λ hΛ σ q t⟩

lemma cavityLabel_full_log_integrable (n d : ℕ) {K : ℝ} {k : ℕ}
    (p : Fin (k+1)→BulkPairRange K) (D : BulkPairRange K)
    (hp0 : ∀ i,0≤cavityPairProfile n d p 0 i)
    (hpm : ∀ i,Monotone (fun l=>cavityPairProfile n d p l i))
    (hpD : ∀ i,cavityPairProfile n d p (Fin.last k) i≤cavityPairDiagonal n d D i)
    (f : ℝ→ᵇℝ) (z : Fin k→ℝ) :
    let σ:=fun i=>Real.sqrt (cavityPairDiagonal n d D i-cavityPairProfile n d p (Fin.last k) i)
    Integrable (fun t=>Real.log (cavityLabelFullPartition n d k f σ (cavityPairProfile n d p) t))
      ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod countableGaussianLaw) := by
  have h := (cavityLabel_uncap_annealed n d p D hp0 hpm hpD f z (Λ:=1) le_rfl).1
  have hb := cavityLabel_capped_log_integrable n d k f 1 le_rfl (fun i=>Real.sqrt (cavityPairDiagonal n d D i-cavityPairProfile n d p (Fin.last k) i)) (cavityPairProfile n d p) z
  exact (h.add hb).congr (ae_of_all _ fun t=>sub_add_cancel _ _)

end SphericalPerceptronFreeEnergy

end

end OAI
