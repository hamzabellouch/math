import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityLabelArray

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction

section

variable {S : Type} [MeasurableSpace S]

def cavityCompletedCountableVector (n : ℕ) (v : ℕ→S→ℝ) (L : S→ℕ)
    (σ : Fin (n+1)→ℝ) (xs : Fin (n+1)→S)
    (p : (ℕ→ℝ)×Spin (n+1)) : Spin (n+1) :=
  WithLp.toLp 2 (fun i=>countableGaussianField v L p.1 (xs i)+σ i*p.2 i)

omit [MeasurableSpace S] in
lemma cavityCompletedCountableVector_measurable (n : ℕ) (v : ℕ→S→ℝ) (L : S→ℕ)
    (σ : Fin (n+1)→ℝ) (xs : Fin (n+1)→S) :
    Measurable (cavityCompletedCountableVector n v L σ xs) := by
  apply (MeasurableEquiv.toLp 2 (Fin (n+1)→ℝ)).measurable.comp
  apply Measurable.of_eval
  intro i
  dsimp [cavityCompletedCountableVector,countableGaussianField,gaussianPrefixField]
  fun_prop

lemma cavityCompletedCountableVector_law (n : ℕ) (v : ℕ→S→ℝ) (L : S→ℕ)
    (σ : Fin (n+1)→ℝ) (xs : Fin (n+1)→S)
    (w : Fin (n+1)→Spin (n+1))
    (hc : ∀ i j,countableGaussianCovariance v v L (xs i) (xs j)+
      (if i=j then σ i^2 else 0)=inner ℝ (w i) (w j)) :
    (countableGaussianLaw.prod (stdGaussian (Spin (n+1)))).map
      (cavityCompletedCountableVector n v L σ xs)=
      (stdGaussian (Spin (n+1))).map (gaussianRows w) := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro Ψ
  have hm := cavityCompletedCountableVector_measurable n v L σ xs
  rw [integral_map hm.aemeasurable Ψ.continuous.aestronglyMeasurable,
    integral_map (gaussianRows w).measurable.aemeasurable Ψ.continuous.aestronglyMeasurable]
  have hi : Integrable (fun p=>Ψ (cavityCompletedCountableVector n v L σ xs p))
      (countableGaussianLaw.prod (stdGaussian (Spin (n+1)))) :=
    Integrable.of_bound (Ψ.measurable.comp hm).aestronglyMeasurable ‖Ψ‖
      (ae_of_all _ fun p=>Ψ.norm_coe_le_norm _)
  rw [integral_prod _ hi]
  change (∫ g,cavityDiagonalAverage σ Ψ
    (WithLp.toLp 2 (fun i=>countableGaussianField v L g (xs i))) ∂countableGaussianLaw)=_
  rw [cavity_countable_kernel_diagonal_noise]
  have he : (fun i j=>countableGaussianCovariance v v L (xs i) (xs j)+
      if i=j then σ i^2 else 0)=Matrix.gram ℝ w := by
    ext i j
    exact hc i j
  rw [he,cavityMatrixKernel_posSemidef _ _ (Matrix.posSemidef_gram ℝ w),
    ←gaussianRows_map_stdGaussian,
    integral_map (gaussianRows w).measurable.aemeasurable Ψ.continuous.aestronglyMeasurable]

lemma cavityCompletedCountableVector_isotropic (n : ℕ) (v : ℕ→S→ℝ) (L : S→ℕ)
    (σ : Fin (n+1)→ℝ) (xs : Fin (n+1)→S) {b : ℝ} (hb : 0≤b)
    (hc : ∀ i j,countableGaussianCovariance v v L (xs i) (xs j)+
      (if i=j then σ i^2 else 0)=if i=j then b else 0) :
    (countableGaussianLaw.prod (stdGaussian (Spin (n+1)))).map
      (cavityCompletedCountableVector n v L σ xs)=
      (stdGaussian (Spin (n+1))).map (fun z=>Real.sqrt b •z) := by
  let w : Fin (n+1)→Spin (n+1):=fun i=>Real.sqrt b •EuclideanSpace.single i (1:ℝ)
  have hw : ∀ i j,inner ℝ (w i) (w j)=if i=j then b else 0 := by
    intro i j
    dsimp only [w]
    simp only [inner_smul_left,inner_smul_right,conj_trivial]
    by_cases h : i=j
    · subst j
      simp [Real.sq_sqrt hb,←pow_two]
    · simp [EuclideanSpace.inner_single_left,h]
  rw [cavityCompletedCountableVector_law n v L σ xs w (fun i j=>(hc i j).trans (hw i j).symm)]
  exact gaussianRows_isotropic_law n w hb hw

lemma cavityCompletedCountableVector_spherical_average (n : ℕ) (v : ℕ→S→ℝ) (L : S→ℕ)
    (σ : Fin (n+1)→ℝ) (xs : Fin (n+1)→S) {b : ℝ} (hb : 0≤b)
    (hc : ∀ i j,countableGaussianCovariance v v L (xs i) (xs j)+
      (if i=j then σ i^2 else 0)=if i=j then b else 0) (R : ℝ) :
    (∫ p,sphericalExp n (cavityCompletedCountableVector n v L σ xs p) R
      ∂countableGaussianLaw.prod (stdGaussian (Spin (n+1))))=Real.exp (R^2*b/2) := by
  rw [←integral_map (cavityCompletedCountableVector_measurable n v L σ xs).aemeasurable
    (sphericalExp_continuous n R).aestronglyMeasurable,
    cavityCompletedCountableVector_isotropic n v L σ xs hb hc,
    integral_map (by fun_prop) (sphericalExp_continuous n R).aestronglyMeasurable]
  have h:=sphericalExp_gaussian_average n R (Real.sqrt b) 0
  have hz : sphericalExp n 0 R=1 := by simp [sphericalExp]
  simpa only [zero_add,Real.sq_sqrt hb,hz,mul_one] using h

lemma cavityCompletedCountableVector_spherical_memLp (n : ℕ) (v : ℕ→S→ℝ) (L : S→ℕ)
    (σ : Fin (n+1)→ℝ) (xs : Fin (n+1)→S) {b : ℝ} (hb : 0≤b)
    (hc : ∀ i j,countableGaussianCovariance v v L (xs i) (xs j)+
      (if i=j then σ i^2 else 0)=if i=j then b else 0) (R : ℝ) :
    MemLp (fun p=>sphericalExp n (cavityCompletedCountableVector n v L σ xs p) R) 2
      (countableGaussianLaw.prod (stdGaussian (Spin (n+1)))) := by
  have hm := (sphericalExp_continuous n R).measurable.comp
    (cavityCompletedCountableVector_measurable n v L σ xs)
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  have hi : Integrable (fun p=>sphericalExp n (cavityCompletedCountableVector n v L σ xs p) (2*R))
      (countableGaussianLaw.prod (stdGaussian (Spin (n+1)))) := by
    by_contra hn
    have h:=cavityCompletedCountableVector_spherical_average n v L σ xs hb hc (2*R)
    rw [integral_undef hn] at h
    exact (Real.exp_pos _).ne' h.symm
  apply hi.mono' (hm.pow_const 2).aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact sphericalExp_square_le n R _

lemma cavityCompletedCountableVector_spherical_second (n : ℕ) (v : ℕ→S→ℝ) (L : S→ℕ)
    (σ : Fin (n+1)→ℝ) (xs : Fin (n+1)→S) {b : ℝ} (hb : 0≤b)
    (hc : ∀ i j,countableGaussianCovariance v v L (xs i) (xs j)+
      (if i=j then σ i^2 else 0)=if i=j then b else 0) (R : ℝ) :
    (∫ p,sphericalExp n (cavityCompletedCountableVector n v L σ xs p) R^2
      ∂countableGaussianLaw.prod (stdGaussian (Spin (n+1))))≤Real.exp (2*R^2*b) := by
  have hs := (memLp_two_iff_integrable_sq
    (cavityCompletedCountableVector_spherical_memLp n v L σ xs hb hc R).aestronglyMeasurable).mp
    (cavityCompletedCountableVector_spherical_memLp n v L σ xs hb hc R)
  have hi := (cavityCompletedCountableVector_spherical_memLp n v L σ xs hb hc (2*R)).integrable (by norm_num)
  apply (integral_mono hs hi (fun p=>sphericalExp_square_le n R _)).trans_eq
  rw [cavityCompletedCountableVector_spherical_average n v L σ xs hb hc]
  congr 1
  ring

end

lemma cavityLabelVector_second_moment (n d : ℕ) {K : ℝ} {k : ℕ}
    (p : Fin (k+1)→BulkPairRange K) (D : BulkPairRange K)
    (hp0 : ∀ i,0≤cavityPairProfile n d p 0 i)
    (hpm : ∀ i,Monotone (fun l=>cavityPairProfile n d p l i))
    (hpD : ∀ i,cavityPairProfile n d p (Fin.last k) i≤cavityPairDiagonal n d D i)
    (x : IndexedLeaf k) (R : ℝ) :
    let V:=cavityCompletedCountableVector n (cavityLabelRow (cavityPairProfile n d p))
      (cavityLabelLength k) (fun _=>Real.sqrt (D.2.val-(p (Fin.last k)).2.val))
      (fun i=>(x,Sum.inl i))
    let P:=countableGaussianLaw.prod (stdGaussian (Spin (n+1)))
    MemLp (fun y=>sphericalExp n (V y) R) 2 P ∧
      (∫ y,sphericalExp n (V y) R^2 ∂P)≤Real.exp (2*R^2*D.2.val) := by
  have htop : (p (Fin.last k)).2.val≤D.2.val := hpD (Sum.inl 0)
  have hb : 0≤D.2.val := (hp0 (Sum.inl 0)).trans
    (((hpm (Sum.inl 0)) (Fin.zero_le (Fin.last k))).trans (hpD (Sum.inl 0)))
  have hc (i j : Fin (n+1)) :
      countableGaussianCovariance (cavityLabelRow (cavityPairProfile n d p))
        (cavityLabelRow (cavityPairProfile n d p)) (cavityLabelLength k)
        (x,Sum.inl i) (x,Sum.inl j)+
        (if i=j then (Real.sqrt (D.2.val-(p (Fin.last k)).2.val))^2 else 0)=
        if i=j then D.2.val else 0 := by
    rw [cavityLabel_covariance _ hp0 hpm]
    simp only [Sum.inl.injEq,indexedCommonDepth_self]
    by_cases h : i=j
    · simp only [h,ite_true,Real.sq_sqrt (sub_nonneg.mpr htop),cavityPairProfile,Sum.elim_inl]
      ring
    · simp [h]
  exact ⟨cavityCompletedCountableVector_spherical_memLp n _ _ _ _ hb hc R,
    cavityCompletedCountableVector_spherical_second n _ _ _ _ hb hc R⟩

end SphericalPerceptronFreeEnergy
end

end OAI
