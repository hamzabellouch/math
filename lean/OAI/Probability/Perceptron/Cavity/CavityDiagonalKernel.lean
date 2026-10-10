import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityNormalizedIncrement

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction

section

variable {I : Type} [Fintype I] [DecidableEq I]

def cavityDiagonalAverage (σ : I→ℝ) (Ψ : EuclideanSpace ℝ I→ᵇℝ) : EuclideanSpace ℝ I→ᵇℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x=>∫ z,Ψ (WithLp.toLp 2 (fun i=>x i+σ i*z i)) ∂stdGaussian (EuclideanSpace ℝ I),by
      apply continuous_of_dominated (bound:=fun _=>‖Ψ‖)
      · intro x
        have hm : Measurable (fun z : EuclideanSpace ℝ I=>Ψ (WithLp.toLp 2 (fun i=>x i+σ i*z i))) := by fun_prop
        exact (Integrable.of_bound hm.aestronglyMeasurable ‖Ψ‖ (ae_of_all _ fun z=>Ψ.norm_coe_le_norm _)).aestronglyMeasurable
      · intro x
        exact ae_of_all _ fun z=>Ψ.norm_coe_le_norm _
      · exact integrable_const _
      · exact ae_of_all _ fun z=>by fun_prop⟩
    (2*‖Ψ‖) (by
      intro x y
      have hx : ‖∫ z,Ψ (WithLp.toLp 2 (fun i=>x i+σ i*z i)) ∂stdGaussian (EuclideanSpace ℝ I)‖≤‖Ψ‖ :=
        by simpa using (norm_integral_le_of_norm_le_const (μ:=stdGaussian (EuclideanSpace ℝ I))
          (ae_of_all _ fun z=>Ψ.norm_coe_le_norm (WithLp.toLp 2 (fun i=>x i+σ i*z i))))
      have hy : ‖∫ z,Ψ (WithLp.toLp 2 (fun i=>y i+σ i*z i)) ∂stdGaussian (EuclideanSpace ℝ I)‖≤‖Ψ‖ :=
        by simpa using (norm_integral_le_of_norm_le_const (μ:=stdGaussian (EuclideanSpace ℝ I))
          (ae_of_all _ fun z=>Ψ.norm_coe_le_norm (WithLp.toLp 2 (fun i=>y i+σ i*z i))))
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans (by dsimp only [ContinuousMap.coe_mk]; linarith))

def cavityNoiseRows {n : ℕ} (v : I→EuclideanSpace ℝ (Fin n)) (σ : I→ℝ) (i : I) :
    EuclideanSpace ℝ (Fin n⊕I) :=
  WithLp.toLp 2 (Sum.elim (fun j=>v i j) (fun j=>if j=i then σ i else 0))

lemma cavityNoiseRows_gram {n : ℕ} (v : I→EuclideanSpace ℝ (Fin n)) (σ : I→ℝ) :
    Matrix.gram ℝ (cavityNoiseRows v σ)=fun i j=>Matrix.gram ℝ v i j+if i=j then σ i^2 else 0 := by
  ext i j
  change (∑ t : Fin n⊕I,Sum.elim (fun t=>v j t) (fun t=>if t=j then σ j else 0) t*
    Sum.elim (fun t=>v i t) (fun t=>if t=i then σ i else 0) t)=_
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  by_cases h : i=j
  · subst j
    simp only [ite_true]
    simp [Matrix.gram,PiLp.inner_apply,pow_two]
  · simp only [ite_eq_right h,zero_mul]
    rfl

lemma cavityNoiseRows_apply {n : ℕ} (v : I→EuclideanSpace ℝ (Fin n)) (σ : I→ℝ)
    (y : EuclideanSpace ℝ (Fin n⊕I)) (i : I) :
    inner ℝ (cavityNoiseRows v σ i) y=
      inner ℝ (v i) (gaussianSumSplit y).1+σ i*(gaussianSumSplit y).2 i := by
  change (∑ t : Fin n⊕I,y t*Sum.elim (fun j=>v i j) (fun j=>if j=i then σ i else 0) t)=_
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  change (∑ t : Fin n,y (Sum.inl t)*v i t)+y (Sum.inr i)*σ i=
    (∑ t : Fin n,y (Sum.inl t)*v i t)+σ i*y (Sum.inr i)
  ring

theorem cavityMatrixKernel_diagonal_noise {n : ℕ}
    (v : I→EuclideanSpace ℝ (Fin n)) (σ : I→ℝ) (Ψ : EuclideanSpace ℝ I→ᵇℝ) :
    cavityMatrixKernel Ψ (fun i j=>Matrix.gram ℝ v i j+if i=j then σ i^2 else 0)=
      cavityMatrixKernel (cavityDiagonalAverage σ Ψ) (Matrix.gram ℝ v) := by
  rw [←cavityNoiseRows_gram v σ,
    cavityMatrixKernel_posSemidef _ _ (Matrix.posSemidef_gram ℝ _),
    ←gaussianRows_map_stdGaussian,
    integral_map (by fun_prop) Ψ.continuous.aestronglyMeasurable]
  let F : EuclideanSpace ℝ (Fin n)×EuclideanSpace ℝ I→ℝ:=fun p=>
    Ψ (WithLp.toLp 2 (fun i=>inner ℝ (v i) p.1+σ i*p.2 i))
  have hm : Measurable F := by fun_prop
  have hi : Integrable F ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod (stdGaussian (EuclideanSpace ℝ I))) :=
    Integrable.of_bound hm.aestronglyMeasurable ‖Ψ‖ (ae_of_all _ fun p=>Ψ.norm_coe_le_norm _)
  have hp:=gaussianSumSplit_preserving (I:=Fin n) (J:=I)
  have he (y : EuclideanSpace ℝ (Fin n⊕I)) : Ψ (gaussianRows (cavityNoiseRows v σ) y)=F (gaussianSumSplit y) := by
    congr 1
    ext i
    exact cavityNoiseRows_apply v σ y i
  simp_rw [he]
  have hmap : (∫ y,F (gaussianSumSplit y) ∂stdGaussian (EuclideanSpace ℝ (Fin n⊕I)))=
      ∫ p,F p ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).prod (stdGaussian (EuclideanSpace ℝ I)) := by
    rw [←hp.map_eq,integral_map hp.measurable.aemeasurable hm.aestronglyMeasurable]
  rw [hmap,integral_prod _ hi,
    cavityMatrixKernel_posSemidef _ _ (Matrix.posSemidef_gram ℝ _),
    ←gaussianRows_map_stdGaussian,
    integral_map (by fun_prop) (cavityDiagonalAverage σ Ψ).continuous.aestronglyMeasurable]
  rfl

theorem cavity_countable_kernel_diagonal_noise {S : Type} [MeasurableSpace S]
    (v : ℕ→S→ℝ) (L : S→ℕ) (σ : I→ℝ) (Ψ : EuclideanSpace ℝ I→ᵇℝ) (xs : I→S) :
    (∫ g,cavityDiagonalAverage σ Ψ (WithLp.toLp 2 (fun i=>countableGaussianField v L g (xs i)))
      ∂countableGaussianLaw)=
    cavityMatrixKernel Ψ (fun i j=>countableGaussianCovariance v v L (xs i) (xs j)+if i=j then σ i^2 else 0) := by
  rw [cavity_countable_kernel]
  have hc : ∀ᶠ n : ℕ in atTop,∀ i j : I,
      gaussianPrefixCovariance v v L n (xs i) (xs j)=countableGaussianCovariance v v L (xs i) (xs j) :=
    Filter.eventually_all.mpr (fun i=>Filter.eventually_all.mpr (fun j=>
      gaussianPrefixCovariance_eventually_eq v v L (xs i) (xs j)))
  obtain ⟨n,hn⟩:=hc.exists
  let rows : I→EuclideanSpace ℝ (Fin n):=fun i=>WithLp.toLp 2 (fun j=>maskedGaussianCoefficient v L j.val (xs i))
  have hg : Matrix.gram ℝ rows=(fun i j=>countableGaussianCovariance v v L (xs i) (xs j)) := by
    ext i j
    rw [←hn i j]
    change (∑ l : Fin n,maskedGaussianCoefficient v L l.val (xs j)*
      maskedGaussianCoefficient v L l.val (xs i))=_
    exact Finset.sum_congr rfl fun l _=>mul_comm _ _
  have hh:=cavityMatrixKernel_diagonal_noise rows σ Ψ
  rw [hg] at hh
  exact hh.symm

end

variable {J : Type} [Fintype J] [DecidableEq J]

def cavityReplicaSplit (r : ℕ) (z : EuclideanSpace ℝ (J×Fin r)) :
    Fin r→EuclideanSpace ℝ J := fun i=>WithLp.toLp 2 (fun j=>z (j,i))

omit [DecidableEq J] in
lemma cavityReplicaSplit_preserving [DecidableEq J] (r : ℕ) :
    MeasurePreserving (cavityReplicaSplit (J:=J) r)
      (stdGaussian (EuclideanSpace ℝ (J×Fin r)))
      (Measure.pi fun _ : Fin r=>stdGaussian (EuclideanSpace ℝ J)) := by
  have ho : MeasurePreserving (WithLp.ofLp : EuclideanSpace ℝ (J×Fin r)→(J×Fin r→ℝ))
      (stdGaussian (EuclideanSpace ℝ (J×Fin r)))
      (Measure.pi fun _ : J×Fin r=>gaussianReal 0 1) := by
    refine ⟨(PiLp.continuous_ofLp 2 _).measurable,?_⟩
    rw [←map_pi_eq_stdGaussian,Measure.map_map (PiLp.continuous_ofLp 2 _).measurable
      (PiLp.continuous_toLp 2 _).measurable]
    exact Measure.map_id
  have hs:=measurePreserving_piCongrLeft (fun _ : Fin r×J=>gaussianReal 0 1) (Equiv.prodComm J (Fin r))
  have hc : MeasurePreserving (MeasurableEquiv.curry (Fin r) J ℝ)
      (Measure.pi fun _ : Fin r×J=>gaussianReal 0 1)
      (Measure.pi fun _ : Fin r=>Measure.pi fun _ : J=>gaussianReal 0 1) := by
    refine ⟨(MeasurableEquiv.curry _ _ _).measurable,?_⟩
    simpa only [Measure.infinitePi_eq_pi] using
      Measure.infinitePi_map_curry (fun (_ : Fin r) (_ : J)=>gaussianReal 0 1)
  have ht : MeasurePreserving (WithLp.toLp 2 : (J→ℝ)→EuclideanSpace ℝ J)
      (Measure.pi fun _ : J=>gaussianReal 0 1) (stdGaussian (EuclideanSpace ℝ J)) :=
    ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩
  have hp:=measurePreserving_pi (fun _ : Fin r=>Measure.pi fun _ : J=>gaussianReal 0 1)
    (fun _ : Fin r=>stdGaussian (EuclideanSpace ℝ J)) (fun _=>ht)
  convert hp.comp (hc.comp (hs.comp ho)) using 1
  rfl

lemma cavityDiagonalAverage_replica (σ : J→ℝ) (Ψ : EuclideanSpace ℝ J→ᵇℝ) (r : ℕ) :
    cavityDiagonalAverage (fun p : J×Fin r=>σ p.1) (cavityTestReplica Ψ r)=
      cavityTestReplica (cavityDiagonalAverage σ Ψ) r := by
  ext x
  let F : (Fin r→EuclideanSpace ℝ J)→ℝ := fun y=>
    ∏ i : Fin r,Ψ (WithLp.toLp 2 (fun j=>x (j,i)+σ j*y i j))
  have hm : Measurable F := by fun_prop
  have hp:=cavityReplicaSplit_preserving (J:=J) r
  change (∫ z,cavityTestReplica Ψ r (WithLp.toLp 2 (fun p=>x p+σ p.1*z p))
    ∂stdGaussian (EuclideanSpace ℝ (J×Fin r)))=_
  simp only [cavityTestReplica_apply]
  have he (z : EuclideanSpace ℝ (J×Fin r)) :
      (∏ i : Fin r,Ψ (WithLp.toLp 2 (fun j=>(WithLp.toLp 2 (fun p : J×Fin r=>x p+σ p.1*z p)) (j,i))))=
        F (cavityReplicaSplit r z) := rfl
  simp_rw [he]
  rw [←integral_map hp.measurable.aemeasurable hm.aestronglyMeasurable,hp.map_eq]
  exact integral_fintype_prod_eq_prod (fun (i : Fin r) (y : EuclideanSpace ℝ J)=>Ψ (WithLp.toLp 2 (fun j=>x (j,i)+σ j*y j)))

theorem cavity_countable_residual_moment {S : Type} [MeasurableSpace S]
    [MeasurableSpace J] (μ : Measure S) [IsProbabilityMeasure μ]
    (v : ℕ→S×J→ℝ) (L : S×J→ℕ)
    (hv : ∀ i,Measurable (v i)) (hL : Measurable L)
    (σ : J→ℝ) (Ψ : EuclideanSpace ℝ J→ᵇℝ) (r : ℕ) :
    (∫ g,(∫ x,cavityDiagonalAverage σ Ψ (cavityCountableField v L g x) ∂μ)^r
      ∂countableGaussianLaw)=
      ∫ xs : Fin r→S,cavityMatrixKernel (cavityTestReplica Ψ r)
        (fun p q : J×Fin r=>countableGaussianCovariance v v L (xs p.2,p.1) (xs q.2,q.1)+
          if p=q then σ p.1^2 else 0) ∂Measure.pi (fun _=>μ) := by
  rw [cavity_countable_moment μ v L hv hL,←cavityDiagonalAverage_replica]
  apply integral_congr_ae
  exact ae_of_all _ fun xs=>by
    dsimp only
    rw [←cavity_countable_kernel v L (cavityDiagonalAverage (fun p : J×Fin r=>σ p.1) (cavityTestReplica Ψ r)) (fun p : J×Fin r=>(xs p.2,p.1))]
    exact cavity_countable_kernel_diagonal_noise v L (fun p : J×Fin r=>σ p.1)
      (cavityTestReplica Ψ r) (fun p : J×Fin r=>(xs p.2,p.1))

end SphericalPerceptronFreeEnergy
end

end OAI
