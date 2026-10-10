import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityGaussianReplica

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction

abbrev CavityBulkNoiseIndex (n d m M : ℕ) :=
  (Fin (n+1) ⊕ Fin d) × (Fin M ⊕ Fin (m+1))

def cavityBulkBase (n d m M : ℕ) (f : Jet3) (a : BulkDisorder (m+1) M)
    (x : NormalizedSpin (m+1)) (j : Fin (n+1)⊕Fin d) (k : Fin M⊕Fin (m+1)) : ℝ :=
  match j,k with
  | Sum.inl _,Sum.inl t => (Real.sqrt (m+1:ℕ))⁻¹*f.d1 (inner ℝ x.val (WithLp.toLp 2 (a.1 t)))
  | Sum.inr _,Sum.inr t => x.val t
  | _,_ => 0

def cavityBulkFeature (n d m M : ℕ) (f : Jet3) (a : BulkDisorder (m+1) M)
    (x : NormalizedSpin (m+1)) (j : Fin (n+1)⊕Fin d) :
    EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M) :=
  WithLp.toLp 2 (fun p=>if p.1=j then cavityBulkBase n d m M f a x j p.2 else 0)

lemma cavityBulkFeature_measurable (n d m M : ℕ) (f : Jet3) :
    Measurable (fun p : BulkDisorder (m+1) M×NormalizedSpin (m+1)=>
      cavityBulkFeature n d m M f p.1 p.2) := by
  apply Measurable.of_eval
  intro j
  unfold cavityBulkFeature
  apply (MeasurableEquiv.toLp 2 (CavityBulkNoiseIndex n d m M→ℝ)).measurable.comp
  apply Measurable.of_eval
  intro p
  split_ifs
  · cases j <;> cases p.2 <;> dsimp [cavityBulkBase] <;> fun_prop
  · exact measurable_const

lemma cavityBulkFeature_inner (n d m M : ℕ) (f : Jet3) (a : BulkDisorder (m+1) M)
    (x y : NormalizedSpin (m+1)) (j k : Fin (n+1)⊕Fin d) :
    inner ℝ (cavityBulkFeature n d m M f a x j) (cavityBulkFeature n d m M f a y k)=
      if j=k then Sum.elim (fun _=>bulkB (m+1) M f a.1 x y)
        (fun _=>inner ℝ x.val y.val) j else 0 := by
  classical
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct,star_trivial,cavityBulkFeature]
  rw [Fintype.sum_prod_type]
  by_cases hjk : j=k
  · subst k
    simp only [ite_true]
    have he (p : Fin (n+1)⊕Fin d) :
        (∑ t : Fin M⊕Fin (m+1),
          (if p=j then cavityBulkBase n d m M f a y j t else 0)*
          (if p=j then cavityBulkBase n d m M f a x j t else 0))=
        if p=j then ∑ t : Fin M⊕Fin (m+1),
          cavityBulkBase n d m M f a y j t*cavityBulkBase n d m M f a x j t else 0 := by
      split_ifs <;> simp_all
    simp_rw [he]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ,ite_true]
    cases j with
    | inl _index =>
      simp only [Fintype.sum_sum_type,cavityBulkBase,Sum.elim_inl,mul_zero,Finset.sum_const_zero,add_zero]
      unfold bulkB
      rw [Finset.mul_sum]
      simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]
      apply Finset.sum_congr rfl
      intro i _hi
      have hn : (0:ℝ)<(m+1:ℕ) := by positivity
      have hs : Real.sqrt ((m+1:ℕ):ℝ)^2=(m+1:ℕ) := Real.sq_sqrt hn.le
      have hp : Real.sqrt ((m+1:ℕ):ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr hn)
      field_simp
      rw [hs]
      ring
    | inr _index =>
      simp only [Fintype.sum_sum_type,cavityBulkBase,Sum.elim_inr,mul_zero,Finset.sum_const_zero,zero_add]
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      rfl
  · rw [ite_eq_right hjk]
    apply Finset.sum_eq_zero
    intro p _hp
    apply Finset.sum_eq_zero
    intro t _ht
    by_cases hpj : p=j
    · subst p
      simp [hjk]
    · simp [hpj]

lemma cavityBulkFeature_gram (n d r m M : ℕ) (f : Jet3) (a : BulkDisorder (m+1) M)
    (x : Fin r→NormalizedSpin (m+1)) (K : ℝ) (hK : M/(m+1:ℕ)*‖f.d1‖^2≤K) :
    Matrix.gram ℝ (fun p : CavityReplicaIndex n d r=>cavityBulkFeature n d m M f a (x p.2) p.1)=
      fun i j=> if i.1=j.1 then
        Sum.elim (fun _=>(bulkMarkedEntry m M f K hK a (x i.2) (x j.2)).2.val)
          (fun _=>(bulkMarkedEntry m M f K hK a (x i.2) (x j.2)).1.val) i.1 else 0 := by
  ext i j
  exact cavityBulkFeature_inner n d m M f a (x i.2) (x j.2) i.1 j.1

lemma cavity_gibbs_moment {S J E : Type*} [MeasurableSpace S]
    [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure S) [IsProbabilityMeasure μ]
    (v : S→J→E) (hv : Measurable v) (H : S→ℝ) (hH : Measurable H)
    (he : Integrable (fun x=>Real.exp (H x)) μ) (Ψ : EuclideanSpace ℝ J→ᵇℝ) (r : ℕ) :
    (∫ y,(tiltMean μ H (fun x=>Ψ (gaussianRows (v x) y)) 1)^r ∂stdGaussian E)=
      gibbsReplicaMean μ H r (fun xs=>cavityMatrixKernel (cavityTestReplica Ψ r)
        (Matrix.gram ℝ (fun p : J×Fin r=>v (xs p.2) p.1))) := by
  have he1 : Integrable (fun x=>Real.exp (1*H x)) μ := by simpa only [one_mul] using he
  let := tilt_law_probability_of_integrable μ he1
  simp_rw [←tilt_law_integral_of_integrable μ hH he1]
  rw [gibbsReplicaMean_integral_of_integrable μ hH he]
  simpa only [Real.exp_zero,one_mul,Finset.prod_const_one] using
    cavity_marked_moment (tiltLaw μ H 1) v hv (fun _=>0) measurable_const
      (C:=0) (fun _=>by simp) Ψ r

def cavityBulkPartition (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (p : BulkDisorder (m+1) M×EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) : ℝ :=
  tiltMean (unitSphereLaw (m+1)) (bulkGibbsHamiltonian m M f.f v p.1)
    (fun x=>cavitySingleTest n d f.f Λ hΛ (gaussianRows (cavityBulkFeature n d m M f p.1 x) p.2)) 1

lemma cavity_rows_joint_measurable {A J E : Type*} [MeasurableSpace A]
    [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {v : A→J→E} {y : A→E}
    (hv : Measurable v) (hy : Measurable y) :
    Measurable (fun a=>gaussianRows (v a) (y a)) := by
  change Measurable (fun a=>WithLp.toLp 2 (fun j=>inner ℝ (v a j) (y a)))
  apply (MeasurableEquiv.toLp 2 (J→ℝ)).measurable.comp
  apply Measurable.of_eval
  intro j
  exact ((measurable_pi_apply j).comp hv).inner hy

lemma cavity_partition_joint_measurable {A S J E : Type*}
    [MeasurableSpace A] [MeasurableSpace S] [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure S) [SFinite μ]
    (v : A→S→J→E) (hv : Measurable (Function.uncurry v))
    (H : A→S→ℝ) (hH : Measurable (Function.uncurry H)) (Ψ : EuclideanSpace ℝ J→ᵇℝ) :
    Measurable (fun p : A×E=>tiltMean μ (H p.1)
      (fun x=>Ψ (gaussianRows (v p.1 x) p.2)) 1) := by
  let κ : Kernel (A×E) S := Kernel.const _ μ
  have hproj : Measurable (fun p : (A×E)×S=>(p.1.1,p.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  apply kernel_tiltMean_measurable κ (H:=fun p x=>H p.1 x)
    (Y:=fun p x=>Ψ (gaussianRows (v p.1 x) p.2)) (hH.comp hproj)
  exact Ψ.measurable.comp (cavity_rows_joint_measurable (hv.comp hproj) measurable_fst.snd)

lemma cavityBulkPartition_measurable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) : Measurable (cavityBulkPartition n d m M f v Λ hΛ) := by
  exact cavity_partition_joint_measurable (unitSphereLaw (m+1))
    (cavityBulkFeature n d m M f) (cavityBulkFeature_measurable n d m M f)
    (bulkGibbsHamiltonian m M f.f v) (bulkGibbsHamiltonian_measurable m M f.f v)
    (cavitySingleTest n d f.f Λ hΛ)

def cavityBulkMoment (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ) (r : ℕ) : ℝ :=
  ∫ a,∫ y,(cavityBulkPartition n d m M f v Λ hΛ (a,y))^r
    ∂stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) ∂bulkDisorderLaw (m+1) M

lemma cavityBulkMoment_array (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (K : ℝ) (hK : M/(m+1:ℕ)*‖f.d1‖^2≤K) (r : ℕ) :
    cavityBulkMoment n d m M f v Λ hΛ r=
      ∫ Q,cavityArrayKernel n d r f.f Λ hΛ K Q ∂bulkMarkedArrayLaw m M f v K hK := by
  let F : CompactBlock (BulkPairRange K) r→ᵇℝ :=
    (cavityMatrixKernel (cavityReplicaTest n d r f.f Λ hΛ)).compContinuous
      ⟨fun Q=>fun i j : CavityReplicaIndex n d r=>if i.1=j.1 then
        Sum.elim (fun _=>(Q i.2 j.2).2.val) (fun _=>(Q i.2 j.2).1.val) i.1 else 0,by
          apply continuous_pi
          intro i
          apply continuous_pi
          intro j
          split_ifs
          · cases i.1 <;> dsimp only [Sum.elim] <;> fun_prop
          · exact continuous_const⟩
  have hb := bulkMarkedArray_block m M f v K hK r F
  change (∫ Q,cavityArrayKernel n d r f.f Λ hΛ K Q ∂bulkMarkedArrayLaw m M f v K hK)=_ at hb
  rw [hb]
  unfold cavityBulkMoment bulkReplicaMean
  apply integral_congr_ae
  filter_upwards [] with a
  have he := bulkHamiltonian_exp_integrable m M f.f v a
  have hv : Measurable (cavityBulkFeature n d m M f a) :=
    (cavityBulkFeature_measurable n d m M f).of_uncurry_left
  rw [show (∫ y,cavityBulkPartition n d m M f v Λ hΛ (a,y)^r ∂stdGaussian _)=
      gibbsReplicaMean (unitSphereLaw (m+1)) (bulkGibbsHamiltonian m M f.f v a) r
        (fun xs=>cavityMatrixKernel (cavityTestReplica (cavitySingleTest n d f.f Λ hΛ) r)
          (Matrix.gram ℝ (fun p : (Fin (n+1)⊕Fin d)×Fin r=>
            cavityBulkFeature n d m M f a (xs p.2) p.1))) from
      cavity_gibbs_moment _ _ hv _ (bulkGibbsHamiltonian_measurable m M f.f v).of_uncurry_left he _ r]
  rw [cavitySingleTest_replica]
  apply congrArg (gibbsReplicaMean _ _ r)
  funext xs
  rw [cavityBulkFeature_gram n d r m M f a xs K hK]
  rfl

theorem cavityBulkMoment_tendsto (n d : ℕ) (M : ℕ→ℕ) (f : Jet3) (v : ℕ→ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (K : ℝ) (hK : ∀ m,M m/(m+1:ℕ)*‖f.d1‖^2≤K) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray (BulkPairRange K))}
    (hlim : Tendsto (fun j=>bulkMarkedArrayLaw (s j) (M (s j)) f (v (s j)) K (hK (s j))) atTop (𝓝 ν))
    (r : ℕ) :
    Tendsto (fun j=>cavityBulkMoment n d (s j) (M (s j)) f (v (s j)) Λ hΛ r) atTop
      (𝓝 (∫ Q,cavityArrayKernel n d r f.f Λ hΛ K Q ∂ν)) := by
  simp_rw [cavityBulkMoment_array n d _ _ f _ Λ hΛ K (hK _)]
  exact cavityArrayKernel_tendsto n d r f.f Λ hΛ K hlim

end SphericalPerceptronFreeEnergy
end

end OAI
