import Mathlib
import OAI.Probability.Perceptron.Cavity.CountableFreshMoment

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal BoundedContinuousFunction ENNReal

section

variable {n r : ℕ}

def freshNoiseRows (v : Fin r→EuclideanSpace ℝ (Fin n)) (s : ℝ≥0) (i : Fin r) :
    EuclideanSpace ℝ (Fin n ⊕ Fin r) :=
  WithLp.toLp 2 (Sum.elim (fun j => v i j) (fun j => if j=i then Real.sqrt s else 0))

lemma freshNoiseRows_apply (v : Fin r→EuclideanSpace ℝ (Fin n)) (s : ℝ≥0)
    (x : Fin n→ℝ) (y : Fin r→ℝ) (i : Fin r) :
    inner ℝ (freshNoiseRows v s i) (WithLp.toLp 2 (Sum.elim x y)) =
      inner ℝ (v i) (WithLp.toLp 2 x) + Real.sqrt s*y i := by
  classical
  change (∑ j : Fin n ⊕ Fin r, Sum.elim x y j *
    Sum.elim (fun j => v i j) (fun j => if j=i then Real.sqrt s else 0) j) = _
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr]
  rw [show (∑ j : Fin r, y j * if j=i then Real.sqrt s else 0)=Real.sqrt s*y i by
    simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]; ring]
  rfl

lemma freshNoiseRows_gram (v : Fin r→EuclideanSpace ℝ (Fin n)) (s : ℝ≥0) :
    Matrix.gram ℝ (freshNoiseRows v s)=fun i j => Matrix.gram ℝ v i j + if i=j then (s:ℝ) else 0 := by
  classical
  ext i j
  change (∑ l : Fin n ⊕ Fin r,
    Sum.elim (fun l => v j l) (fun l => if l=j then Real.sqrt s else 0) l *
    Sum.elim (fun l => v i l) (fun l => if l=i then Real.sqrt s else 0) l)=_
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  by_cases h : i=j
  · subst j
    simp only [ite_true,← sq,Real.sq_sqrt s.coe_nonneg]
    simp [Matrix.gram,PiLp.inner_apply,pow_two]
  · simp only [ite_eq_right h,zero_mul]
    rfl

theorem freshReplicaMatrixKernel_diagonal_noise (f : ℝ →ᵇ ℝ)
    (v : Fin r→EuclideanSpace ℝ (Fin n)) (s : ℝ≥0) :
    freshReplicaMatrixKernel f r (fun i j => Matrix.gram ℝ v i j + if i=j then (s:ℝ) else 0)=
      freshReplicaMatrixKernel (gaussianAverageBCF s f) r (Matrix.gram ℝ v) := by
  classical
  rw [← freshNoiseRows_gram v s,freshReplicaMatrixKernel_gram,
    ← gaussianRows_map_stdGaussian,integral_map (by fun_prop) (by fun_prop),
    ← map_pi_eq_stdGaussian,integral_map (by fun_prop) (by fun_prop)]
  let F : (Fin n→ℝ)×(Fin r→ℝ)→ℝ := fun p =>
    ∏ i : Fin r, f (inner ℝ (v i) (WithLp.toLp 2 p.1)+Real.sqrt s*p.2 i)
  have hF : Integrable F ((Measure.pi fun _ : Fin n => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin r => gaussianReal 0 1)) := by
    apply Integrable.of_bound (by fun_prop) (‖f‖^r)
    exact ae_of_all _ fun p => by
      simp only [F,norm_prod]
      exact (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ => f.norm_coe_le_norm _)).trans_eq
        (by simp)
  have hp := measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n⊕Fin r => gaussianReal 0 1)
  have hm : AEStronglyMeasurable (fun z : Fin n⊕Fin r→ℝ =>
      gaussianReplicaTest f (gaussianRows (freshNoiseRows v s) (WithLp.toLp 2 z)))
      (Measure.pi fun _ => gaussianReal 0 1) := by fun_prop
  rw [← hp.map_eq] at hm ⊢
  rw [integral_map hp.measurable.aemeasurable hm]
  have he : (fun p : (Fin n→ℝ)×(Fin r→ℝ) =>
      gaussianReplicaTest f (gaussianRows (freshNoiseRows v s)
        (WithLp.toLp 2 ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n⊕Fin r => ℝ)).symm p))))=F := by
    funext p
    simp only [gaussianReplicaTest_apply,gaussianRows_apply]
    apply Finset.prod_congr rfl
    intro i hi
    exact congrArg f (freshNoiseRows_apply v s p.1 p.2 i)
  rw [he,integral_prod _ hF]
  have hi (x : Fin n→ℝ) : (∫ y : Fin r→ℝ, F (x,y) ∂Measure.pi (fun _ => gaussianReal 0 1))=
      gaussianReplicaTest (gaussianAverageBCF s f) (gaussianRows v (WithLp.toLp 2 x)) := by
    rw [gaussianReplicaTest_apply]
    change (∫ y : Fin r→ℝ, ∏ i, f (inner ℝ (v i) (WithLp.toLp 2 x)+Real.sqrt s*y i)
      ∂Measure.pi (fun _ => gaussianReal 0 1))=_
    rw [integral_fintype_prod_eq_prod (f := fun i y => f (inner ℝ (v i) (WithLp.toLp 2 x)+Real.sqrt s*y))]
    apply Finset.prod_congr rfl
    intro i hi
    exact (gaussianAverage_scaling s f _).symm
  simp_rw [hi]
  rw [freshReplicaMatrixKernel_gram,← gaussianRows_map_stdGaussian,
    integral_map (by fun_prop) (by fun_prop),← map_pi_eq_stdGaussian,
    integral_map (by fun_prop) (by fun_prop)]

lemma countableGaussianCovariance_finite_gram {S : Type*} [MeasurableSpace S]
    (v : ℕ→S→ℝ) (L : S→ℕ) (r : ℕ) (xs : Fin r→S) :
    ∃ n : ℕ, ∃ w : Fin r→EuclideanSpace ℝ (Fin n),
      Matrix.gram ℝ w=(fun i j => countableGaussianCovariance v v L (xs i) (xs j)) := by
  have hc : ∀ᶠ n : ℕ in Filter.atTop, ∀ i j : Fin r,
      gaussianPrefixCovariance v v L n (xs i) (xs j)=countableGaussianCovariance v v L (xs i) (xs j) :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun j =>
      gaussianPrefixCovariance_eventually_eq v v L (xs i) (xs j)))
  obtain ⟨n,hn⟩ := hc.exists
  refine ⟨n,fun i => WithLp.toLp 2 (fun j : Fin n => maskedGaussianCoefficient v L j.val (xs i)),?_⟩
  ext i j
  rw [← hn i j]
  change (∑ l : Fin n, maskedGaussianCoefficient v L l.val (xs j)*
    maskedGaussianCoefficient v L l.val (xs i))=_
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem countableFresh_moment_diagonal_noise {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (v : ℕ→S→ℝ) (L : S→ℕ)
    (hv : ∀ i, Measurable (v i)) (hL : Measurable L) (f : ℝ →ᵇ ℝ) (s : ℝ≥0) (r : ℕ) :
    (∫ g, (∫ x, gaussianAverageBCF s f (countableGaussianField v L g x) ∂μ)^r ∂countableGaussianLaw)=
      ∫ xs : Fin r→S, freshReplicaMatrixKernel f r
        (fun i j => countableGaussianCovariance v v L (xs i) (xs j) + if i=j then (s:ℝ) else 0)
        ∂Measure.pi (fun _ => μ) := by
  rw [countableFresh_moment μ v L hv hL]
  apply integral_congr_ae
  exact ae_of_all _ fun xs => by
    obtain ⟨n,w,hw⟩ := countableGaussianCovariance_finite_gram v L r xs
    change freshReplicaMatrixKernel (gaussianAverageBCF s f) r
      (fun i j => countableGaussianCovariance v v L (xs i) (xs j)) =
      freshReplicaMatrixKernel f r
        (fun i j => countableGaussianCovariance v v L (xs i) (xs j) + if i=j then (s:ℝ) else 0)
    have he (i j : Fin r) := congrFun (congrFun hw i) j
    simp_rw [← he]
    exact (freshReplicaMatrixKernel_diagonal_noise f w s).symm

end

theorem labelProfile_diagonal_one_moment {S : Type} [MeasurableSpace S] {k : ℕ}
    (q : Fin (k+1)→ℝ) (h0 : 0≤q 0) (hq : Monotone q) (h1 : q (Fin.last k)≤1)
    (μ : Measure (S×IndexedLeaf k)) [IsProbabilityMeasure μ] (f : ℝ →ᵇ ℝ) (r : ℕ) :
    (∫ g, (∫ x, gaussianAverageBCF ⟨1-q (Fin.last k),sub_nonneg.mpr h1⟩ f
      (labelProfileField q g x) ∂μ)^r ∂countableGaussianLaw)=
      ∫ xs : Fin r→S×IndexedLeaf k, freshReplicaMatrixKernel f r
        (fun i j => if i=j then 1 else q (indexedCommonDepth k (xs j).2 (xs i).2))
        ∂Measure.pi (fun _ => μ) := by
  have hh := countableFresh_moment_diagonal_noise μ (labelProfileRow q)
    (indexedGaussianRowLength (I := Fin 1) k)
    (indexedGaussianRow_measurable _ _ measurable_const)
    (indexedGaussianRowLength_measurable k) f ⟨1-q (Fin.last k),sub_nonneg.mpr h1⟩ r
  exact hh.trans (by
    apply integral_congr_ae
    exact ae_of_all _ fun xs => by
      apply congrArg (freshReplicaMatrixKernel f r)
      funext i j
      rw [labelProfile_covariance q h0 hq]
      by_cases hij : i=j
      · subst j
        simp only [ite_true,indexedCommonDepth_self]
        change q (Fin.last k)+(1-q (Fin.last k))=1
        ring
      · simp only [ite_eq_right hij,add_zero])

end SphericalPerceptronFreeEnergy
end

end OAI
