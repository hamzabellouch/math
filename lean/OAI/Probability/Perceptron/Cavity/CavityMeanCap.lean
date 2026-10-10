import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityCompensator
import OAI.Probability.Perceptron.Cavity.CavityShellExpansion

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction

lemma cavity_expected_cap {S G : Type*} [MeasurableSpace S] [MeasurableSpace G]
    (μ : Measure S) (P : Measure G) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (W F : G×S→ℝ) (hW : Measurable W) (hF : Measurable F) {C Λ K : ℝ}
    (hWC : ∀ p,|W p|≤C) (hF1 : ∀ p,1≤F p) (hΛ : 1≤Λ)
    (hFx : ∀ g,MemLp (fun x=>F (g,x)) 2 μ)
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
  have hp g : 0≤D g ∧ D g≤Real.exp (2*C)/Λ*(∫ x,F (g,x)^2 ∂μ) :=
    cavity_capped_log_bound μ (hW.comp (measurable_const.prodMk measurable_id)) (fun x=>hWC (g,x)) (hFx g) (fun x=>hF1 (g,x)) hΛ
  have hc : 0≤Real.exp (2*C)/Λ := div_nonneg (Real.exp_pos _).le ((by norm_num : (0:ℝ)≤1).trans hΛ)
  have hDi : Integrable D P := by
    apply (hS.const_mul (Real.exp (2*C)/Λ)).mono' hD.aestronglyMeasurable
    exact ae_of_all _ fun g=>by simpa only [Real.norm_eq_abs,abs_of_nonneg (hp g).1] using (hp g).2
  refine ⟨hDi,integral_nonneg (fun g=>(hp g).1),?_⟩
  calc
    _≤∫ g,Real.exp (2*C)/Λ*(∫ x,F (g,x)^2 ∂μ) ∂P :=
      integral_mono hDi (hS.const_mul _) (fun g=>(hp g).2)
    _=Real.exp (2*C)/Λ*(∫ g,∫ x,F (g,x)^2 ∂μ ∂P) := integral_const_mul _ _
    _≤_ := mul_le_mul_of_nonneg_left hB hc

lemma cavity_rows_joint_continuous {A J E : Type*} [TopologicalSpace A]
    [Fintype J] [DecidableEq J] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v : A→J→E} {y : A→E} (hv : Continuous v) (hy : Continuous y) :
    Continuous (fun a=>gaussianRows (v a) (y a)) := by
  change Continuous (fun a=>WithLp.toLp 2 (fun i=>inner ℝ (v a i) (y a)))
  apply (PiLp.continuous_toLp 2 _).comp
  exact continuous_pi fun i=>((continuous_apply i).comp hv).inner hy

lemma cavityBulkFeature_continuous (n d m M : ℕ) (f : Jet3) (a : BulkDisorder (m+1) M) :
    Continuous (cavityBulkFeature n d m M f a) := by
  apply continuous_pi
  intro j
  unfold cavityBulkFeature
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro p
  split_ifs
  · cases j <;> cases p.2 <;> dsimp [cavityBulkBase] <;> fun_prop
  · exact continuous_const

def cavityBulkFullCompPartition (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (p : BulkDisorder (m+1) M×EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) : ℝ :=
  tiltMean (unitSphereLaw (m+1)) (bulkGibbsHamiltonian m M f.f v p.1)
    (fun x=>Real.exp ((n+1:ℕ)/2*bulkC (m+1) M f p.1.1 x+
      ∑ t : Fin d,f.f (inner ℝ (cavityBulkFeature n d m M f p.1 x (Sum.inr t)) p.2))*
      sphericalExp n (gaussianRows (fun i=>cavityBulkFeature n d m M f p.1 x (Sum.inl i)) p.2)
        (Real.sqrt (n+1:ℕ))) 1

lemma cavityBulk_full_vector_second (n d m M : ℕ) (f : Jet3) (a : BulkDisorder (m+1) M)
    (x : NormalizedSpin (m+1)) (K : ℝ) (hK : M/(m+1:ℕ)*‖f.d1‖^2≤K) :
    MemLp (fun y=>sphericalExp n
      (gaussianRows (fun i=>cavityBulkFeature n d m M f a x (Sum.inl i)) y)
      (Real.sqrt (n+1:ℕ))) 2 (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M))) ∧
    (∫ y,sphericalExp n
      (gaussianRows (fun i=>cavityBulkFeature n d m M f a x (Sum.inl i)) y)
      (Real.sqrt (n+1:ℕ))^2 ∂stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))≤
      Real.exp (2*(n+1:ℕ)*K) := by
  let w := fun i : Fin (n+1)=>cavityBulkFeature n d m M f a x (Sum.inl i)
  have hw i j : inner ℝ (w i) (w j)=if i=j then bulkB (m+1) M f a.1 x x else 0 := by
    simp only [w,cavityBulkFeature_inner,Sum.inl.injEq,Sum.elim_inl]
  have hb : 0≤bulkB (m+1) M f a.1 x x := by
    have hh : 0 ≤ inner ℝ (w 0) (w 0) := real_inner_self_nonneg
    rwa [hw,ite_eq_left rfl] at hh
  refine ⟨gaussianRows_spherical_memLp n w hb hw _,?_⟩
  apply (gaussianRows_spherical_second n w hb hw _).trans
  apply Real.exp_le_exp.mpr
  rw [Real.sq_sqrt (by positivity : 0≤((n+1:ℕ):ℝ))]
  exact mul_le_mul_of_nonneg_left
    ((le_abs_self _).trans ((bulkB_bound _ _ _ _ _ _).trans hK)) (by positivity)

lemma cavityBulk_unclipped_cap (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (K KC : ℝ)
    (hK : M/(m+1:ℕ)*‖f.d1‖^2≤K)
    (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤KC)
    (a : BulkDisorder (m+1) M) :
    let D:=fun y=>Real.log (cavityBulkFullCompPartition n d m M f v (a,y))-
      Real.log (cavityBulkCompPartition n d m M f v Λ hΛ (a,y))
    Integrable D (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M))) ∧
      (∀ y,0≤D y) ∧ 0≤∫ y,D y ∂stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) ∧
      (∫ y,D y ∂stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))≤
        Real.exp (2*((n+1:ℕ)/2*KC+(d:ℝ)*‖f.f‖)+2*(n+1:ℕ)*K)/Λ := by
  let E:=EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)
  let μ:=tiltLaw (unitSphereLaw (m+1)) (bulkGibbsHamiltonian m M f.f v a) 1
  have he : Integrable (fun x=>Real.exp (1*bulkGibbsHamiltonian m M f.f v a x)) (unitSphereLaw (m+1)) := by
    simpa only [one_mul,bulkGibbsHamiltonian] using bulkHamiltonian_exp_integrable m M f.f v a
  let : IsProbabilityMeasure μ := tilt_law_probability_of_integrable _ he
  let w:=fun x i=>cavityBulkFeature n d m M f a x (Sum.inl i)
  let F : E×NormalizedSpin (m+1)→ℝ:=fun p=>sphericalExp n (gaussianRows (w p.2) p.1) (Real.sqrt (n+1:ℕ))
  let W : E×NormalizedSpin (m+1)→ℝ:=fun p=>(n+1:ℕ)/2*bulkC (m+1) M f a.1 p.2+
    ∑ t : Fin d,f.f (inner ℝ (cavityBulkFeature n d m M f a p.2 (Sum.inr t)) p.1)
  have hw : Continuous w := by
    apply continuous_pi
    intro i
    exact (continuous_apply (Sum.inl i)).comp (cavityBulkFeature_continuous n d m M f a)
  have hFr : Continuous (fun p : E×NormalizedSpin (m+1)=>gaussianRows (w p.2) p.1) :=
    cavity_rows_joint_continuous (hw.comp continuous_snd) continuous_fst
  have hF : Continuous F := (sphericalExp_continuous n _).comp hFr
  have hW : Measurable W := by
    unfold W bulkC
    have hc:=cavityBulkFeature_continuous n d m M f a
    fun_prop
  have hWC p : |W p|≤(n+1:ℕ)/2*KC+(d:ℝ)*‖f.f‖ := by
    calc
      _≤|(n+1:ℕ)/2*bulkC (m+1) M f a.1 p.2|+
        |∑ t : Fin d,f.f (inner ℝ (cavityBulkFeature n d m M f a p.2 (Sum.inr t)) p.1)| := abs_add_le _ _
      _≤(n+1:ℕ)/2*KC+∑ _ : Fin d,‖f.f‖ := by
        apply add_le_add
        · rw [abs_mul,abs_of_nonneg (by positivity : 0≤((n+1:ℕ):ℝ)/2)]
          exact mul_le_mul_of_nonneg_left (hC a p.2) (by positivity)
        · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t ht=>f.f.norm_coe_le_norm _)
      _=_ := by simp
  have hFx y : MemLp (fun x=>F (y,x)) 2 μ :=
    (hF.comp (continuous_const.prodMk continuous_id)).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfg x:=cavityBulk_full_vector_second n d m M f a x K hK
  have hc:=cavity_expected_cap μ (stdGaussian E) W F hW hF.measurable hWC
    (fun p=>one_le_sphericalExp n _ _) hΛ hFx (fun x=>(hfg x).1) (fun x=>(hfg x).2)
  have hH:=(bulkGibbsHamiltonian_measurable m M f.f v).of_uncurry_left (x:=a)
  have hfull y : (∫ x,Real.exp (W (y,x))*F (y,x) ∂μ)=cavityBulkFullCompPartition n d m M f v (a,y) :=
    tilt_law_integral_of_integrable _ hH he
  have hcap y : (∫ x,Real.exp (W (y,x))*min (F (y,x)) Λ ∂μ)=cavityBulkCompPartition n d m M f v Λ hΛ (a,y) := by
    rw [tilt_law_integral_of_integrable _ hH he]
    unfold cavityBulkCompPartition
    congr 1
    funext x
    simp only [W,F,w,cavitySingleTest_apply,gaussianRows_apply,Real.exp_add,Real.exp_sum]
    change Real.exp _ * (∏ t, _) * min (sphericalExp n (WithLp.toLp 2 _) _) Λ = _
    ring_nf
    rfl
  have hp y:=cavity_capped_log_bound μ
    (hW.comp (measurable_const.prodMk measurable_id)) (fun x=>hWC (y,x))
    (hFx y) (fun x=>one_le_sphericalExp n _ _) hΛ
  dsimp only [Function.comp_apply,id_eq] at hc hp ⊢
  simp_rw [hfull,hcap] at hc hp
  refine ⟨hc.1,fun y=>(hp y).1,hc.2.1,hc.2.2.trans_eq ?_⟩
  rw [Real.exp_add]
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
