import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityMeanCap

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavity_comp_partition_unbounded_measurable {A S J E : Type*}
    [MeasurableSpace A] [MeasurableSpace S] [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure S) [SFinite μ]
    (v : A→S→J→E) (hv : Measurable (Function.uncurry v))
    (H C : A→S→ℝ) (hH : Measurable (Function.uncurry H))
    (hC : Measurable (Function.uncurry C)) (t : ℝ) (Ψ : EuclideanSpace ℝ J→ℝ)
    (hΨ : Measurable Ψ) :
    Measurable (fun p : A×E=>tiltMean μ (H p.1)
      (fun x=>Real.exp (t*C p.1 x)*Ψ (gaussianRows (v p.1 x) p.2)) 1) := by
  let κ : Kernel (A×E) S := Kernel.const _ μ
  have hproj : Measurable (fun p : (A×E)×S=>(p.1.1,p.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  apply kernel_tiltMean_measurable κ (H := fun p x=>H p.1 x)
    (Y := fun p x=>Real.exp (t*C p.1 x)*Ψ (gaussianRows (v p.1 x) p.2)) (hH.comp hproj)
  exact ((hC.comp hproj).const_mul t).exp.mul
    (hΨ.comp (cavity_rows_joint_measurable (hv.comp hproj) measurable_fst.snd))

lemma cavityFullSingleTest_measurable (n d : ℕ) (f : ℝ→ᵇℝ) :
    Measurable (fun z : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)=>
      Real.exp (∑ t,f (z (Sum.inr t)))*
        sphericalExp n (WithLp.toLp 2 (fun i=>z (Sum.inl i))) (Real.sqrt (n+1:ℕ))) := by
  apply Measurable.mul (by fun_prop)
  apply (sphericalExp_continuous n _).measurable.comp
  fun_prop

lemma cavityBulkFullCompPartition_measurable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) :
    Measurable (cavityBulkFullCompPartition n d m M f v) := by
  have h:=cavity_comp_partition_unbounded_measurable (unitSphereLaw (m+1))
    (cavityBulkFeature n d m M f) (cavityBulkFeature_measurable n d m M f)
    (bulkGibbsHamiltonian m M f.f v) (fun a x=>bulkC (m+1) M f a.1 x)
    (bulkGibbsHamiltonian_measurable m M f.f v) (bulkC_measurable m M f) ((n+1:ℕ)/2)
    _ (cavityFullSingleTest_measurable n d f.f)
  convert h using 1
  funext p
  unfold cavityBulkFullCompPartition
  congr 1
  funext x
  simp only [Real.exp_add,gaussianRows_apply]
  rw [mul_assoc]
  rfl

def cavityBulkUncapError (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (p : BulkDisorder (m+1) M×EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) : ℝ :=
  Real.log (cavityBulkFullCompPartition n d m M f v p)-
    Real.log (cavityBulkCompPartition n d m M f v Λ hΛ p)

lemma cavityBulkUncapError_measurable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) : Measurable (cavityBulkUncapError n d m M f v Λ hΛ) :=
  (cavityBulkFullCompPartition_measurable n d m M f v).log.sub
    (cavityBulkCompPartition_measurable n d m M f v Λ hΛ).log

theorem cavityBulk_uncap_annealed (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (K KC : ℝ)
    (hK : M/(m+1:ℕ)*‖f.d1‖^2≤K)
    (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤KC) :
    let D:=cavityBulkUncapError n d m M f v Λ hΛ
    let P:=(bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))
    Integrable D P ∧ 0≤∫ p,D p ∂P ∧ (∫ p,D p ∂P)≤
      Real.exp (2*((n+1:ℕ)/2*KC+(d:ℝ)*‖f.f‖)+2*(n+1:ℕ)*K)/Λ := by
  let D:=cavityBulkUncapError n d m M f v Λ hΛ
  let E:=EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)
  let B:=Real.exp (2*((n+1:ℕ)/2*KC+(d:ℝ)*‖f.f‖)+2*(n+1:ℕ)*K)/Λ
  have hsec a:=cavityBulk_unclipped_cap n d m M f v Λ hΛ K KC hK hC a
  have hD : Measurable D:=cavityBulkUncapError_measurable n d m M f v Λ hΛ
  have hnorm a : (∫ y,‖D (a,y)‖ ∂stdGaussian E)=∫ y,D (a,y) ∂stdGaussian E := by
    apply integral_congr_ae
    exact ae_of_all _ fun y=>by
      change ‖D (a,y)‖=D (a,y)
      exact Real.norm_of_nonneg ((hsec a).2.1 y)
  have hi : Integrable D ((bulkDisorderLaw (m+1) M).prod (stdGaussian E)) := by
    apply (integrable_prod_iff hD.aestronglyMeasurable).mpr
    constructor
    · exact ae_of_all _ fun a=>(hsec a).1
    · apply Integrable.of_bound (hD.norm.stronglyMeasurable.integral_prod_right).aestronglyMeasurable B
      filter_upwards [] with a
      rw [hnorm,Real.norm_eq_abs]
      have hp : 0≤∫ y,D (a,y) ∂stdGaussian E := (hsec a).2.2.1
      rw [abs_of_nonneg hp]
      exact (hsec a).2.2.2
  refine ⟨hi,integral_nonneg (fun p=>(hsec p.1).2.1 p.2),?_⟩
  rw [integral_prod _ hi]
  calc
    _≤∫ _ : BulkDisorder (m+1) M,B ∂bulkDisorderLaw (m+1) M :=
      integral_mono hi.integral_prod_left (integrable_const B) (fun a=>(hsec a).2.2.2)
    _=B := by simp

end SphericalPerceptronFreeEnergy
end

end OAI
