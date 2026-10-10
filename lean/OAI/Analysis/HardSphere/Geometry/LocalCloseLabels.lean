import Mathlib
import OAI.Analysis.HardSphere.Geometry.LocalizedNearLabels
import OAI.Analysis.HardSphere.Geometry.SqTwiceSqAbs

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter

variable {n : ℕ} [Nontrivial (Fin n)]

def localCloseLabels (L : Length) (s : ℝ) (v : Torus L) (X : Configuration n L) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i ↦ torusDistance L (X i) v≤5 ∧ nearestParticleDistance L X i ≤ s)

lemma localCloseSmoothCount_nonneg (L : Length) (s : ℝ) (v : Torus L) (X : Configuration n L) :
    0≤localCloseSmoothCount L s v X := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

lemma localCloseSmoothCount_covers (L : Length) {s : ℝ} (hs : 0<s) (v : Torus L) (X : Configuration n L) :
    ((localCloseLabels L s v X).card:ℝ)≤localCloseSmoothCount L s v X := by
  classical
  calc
    _ = ∑ _i∈localCloseLabels L s v X, (1:ℝ) := by simp
    _ = ∑ i∈localCloseLabels L s v X, closeAmplitude L s v X i^2 := by
      apply Finset.sum_congr rfl
      intro i hi
      have hh := (Finset.mem_filter.mp hi).2
      rw [closeAmplitude_one L hs v X i hh.1 hh.2]
      norm_num
    _ ≤ ∑ i, closeAmplitude L s v X i^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ ↦ sq_nonneg _)

lemma closeAmplitude_ne_zero_imp (L : Length) {s : ℝ} (hs : 0<s) (v : Torus L) (X : Configuration n L) (i : Fin n)
    (h : closeAmplitude L s v X i≠0) :
    torusDistance L (X i) v<6 ∧ nearestParticleDistance L X i<2*s :=
  ⟨lt_of_not_ge (fun he ↦ h (closeAmplitude_zero_of_far L s v X i he)),
    lt_of_not_ge (fun he ↦ h (closeAmplitude_zero_of_isolated L hs v X i he))⟩

lemma closeAmplitude_mem_localized (L : Length) {s : ℝ} (hs : 0<s) (A : Finset (Torus L))
    (v : Torus L) (hv : v∈A) (X : Configuration n L) (i : Fin n) (hi : closeAmplitude L s v X i≠0) :
    i∈localizedNearLabels L A s X := by
  classical
  have hh := closeAmplitude_ne_zero_imp L hs v X i hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,⟨⟨v,hv⟩,
    (spatialSiteDistance_le L A (X i) v hv).trans hh.1.le,nearestLabel L X i,nearestLabel_ne L X i,?_⟩⟩
  have hs' : torusDistance L (X (nearestLabel L X i)) (X i)=nearestParticleDistance L X i := by
    simp only [nearestParticleDistance,torusDistance,dist_comm]
  rw [hs']
  exact hh.2.le

lemma closeAmplitude_unique_site (L : Length) (s : ℝ) (A : Finset (Torus L))
    (hA : ∀ v∈A, ∀ w∈A, v≠w → 12<torusDistance L v w)
    (X : Configuration n L) (i : Fin n) {v w : Torus L} (hv : v∈A) (hw : w∈A)
    (hvi : closeAmplitude L s v X i≠0) (hwi : closeAmplitude L s w X i≠0) : v=w := by
  by_contra he
  have hdv : torusDistance L (X i) v<6 := lt_of_not_ge (fun h ↦ hvi (closeAmplitude_zero_of_far L s v X i h))
  have hdw : torusDistance L (X i) w<6 := lt_of_not_ge (fun h ↦ hwi (closeAmplitude_zero_of_far L s w X i h))
  have ht := torusDistance_triangle' L v (X i) w
  have hs' : torusDistance L v (X i)=torusDistance L (X i) v := by simp only [torusDistance,dist_comm]
  rw [hs'] at ht
  linarith only [hdv,hdw,ht,hA v hv w hw he]

theorem localCloseSmoothCount_sum_le (L : Length) {s : ℝ} (hs : 0<s) (A : Finset (Torus L))
    (hA : ∀ v∈A, ∀ w∈A, v≠w → 12<torusDistance L v w) (X : Configuration n L) :
    (∑ v∈A, localCloseSmoothCount L s v X)≤((localizedNearLabels L A s X).card:ℝ) := by
  classical
  simp only [localCloseSmoothCount]
  rw [Finset.sum_comm]
  have hp (i : Fin n) : (∑ v∈A, closeAmplitude L s v X i^2)≤
      if i∈localizedNearLabels L A s X then (1:ℝ) else 0 := by
    by_cases he : ∃ v∈A, closeAmplitude L s v X i≠0
    · obtain ⟨v,hv,hvi⟩ := he
      rw [ite_eq_left (closeAmplitude_mem_localized L hs A v hv X i hvi)]
      rw [Finset.sum_eq_single v]
      · exact (pow_le_pow_left₀ (closeAmplitude_nonneg L s v X i) (closeAmplitude_le_one L s v X i) 2).trans_eq (by norm_num)
      · intro w hw hwv
        have hz : closeAmplitude L s w X i=0 := by
          by_contra hwi
          exact hwv (closeAmplitude_unique_site L s A hA X i hw hv hwi hvi)
        rw [hz]; norm_num
      · exact fun hn ↦ (hn hv).elim
    · rw [Finset.sum_eq_zero (fun v hv ↦ ?_)]
      · split_ifs <;> norm_num
      · have hz : closeAmplitude L s v X i=0 := not_ne_iff.mp (fun h ↦ he ⟨v,hv,h⟩)
        rw [hz]; norm_num
  calc
    _ ≤ ∑ i, if i∈localizedNearLabels L A s X then (1:ℝ) else 0 := Finset.sum_le_sum (fun i _ ↦ hp i)
    _ = _ := by simp

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Convolution NNReal

variable {ι : Type*} [Fintype ι]

def configurationMollify (L : Length) (φ : ContDiffBump (0 : EuclideanConfiguration ι))
    (f : (ι→Torus L)→ℝ) (X : ι→Torus L) : ℝ :=
  ∫ y : EuclideanConfiguration ι, φ.normed volume y*f (X-euclideanProject L y)

lemma configurationMollify_lift (L : Length) (φ : ContDiffBump (0 : EuclideanConfiguration ι))
    (f : (ι→Torus L)→ℝ) :
    (fun x : EuclideanConfiguration ι ↦ configurationMollify L φ f (euclideanProject L x))=
      φ.normed volume ⋆[lsmul ℝ ℝ,volume] (fun x ↦ f (euclideanProject L x)) := by
  funext x
  simp only [configurationMollify,convolution,lsmul_apply,smul_eq_mul,euclideanProject_sub]

lemma configurationMollify_integrable (L : Length) (φ : ContDiffBump (0 : EuclideanConfiguration ι))
    (f : (ι→Torus L)→ℝ) (hf : Continuous f) (X : ι→Torus L) :
    Integrable (fun y : EuclideanConfiguration ι ↦ φ.normed volume y*f (X-euclideanProject L y)) volume :=
  (φ.continuous_normed.mul (hf.comp (continuous_const.sub (euclideanProject_continuous L)))).integrable_of_hasCompactSupport
    (φ.hasCompactSupport_normed.mul_right)

lemma configurationMollify_smooth (L : Length) (φ : ContDiffBump (0 : EuclideanConfiguration ι))
    (f : (ι→Torus L)→ℝ) (hf : Continuous f) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)
      (fun x : EuclideanConfiguration ι ↦ configurationMollify L φ f (euclideanProject L x)) := by
  rw [configurationMollify_lift]
  exact φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) φ.contDiff_normed
    (hf.comp (euclideanProject_continuous L)).locallyIntegrable

lemma configurationMollify_nonneg (L : Length) (φ : ContDiffBump (0 : EuclideanConfiguration ι))
    (f : (ι→Torus L)→ℝ) (hf : ∀ X, 0≤f X) (X : ι→Torus L) :
    0≤configurationMollify L φ f X :=
  integral_nonneg (fun y ↦ mul_nonneg (φ.nonneg_normed y) (hf _))

lemma configurationMollify_lipschitz (L : Length) (φ : ContDiffBump (0 : EuclideanConfiguration ι))
    {f : (ι→Torus L)→ℝ} (hf : Continuous f) {C : ℝ≥0}
    (hLip : LipschitzWith C (fun x : EuclideanConfiguration ι ↦ f (euclideanProject L x))) :
    LipschitzWith C (fun x : EuclideanConfiguration ι ↦ configurationMollify L φ f (euclideanProject L x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,configurationMollify,configurationMollify,←integral_sub
    (configurationMollify_integrable L φ f hf _) (configurationMollify_integrable L φ f hf _)]
  calc
    _ ≤ ∫ z : EuclideanConfiguration ι, φ.normed volume z*((C:ℝ)*dist x y) := by
      apply norm_integral_le_of_norm_le (φ.integrable_normed.mul_const _) (Eventually.of_forall ?_)
      intro z
      rw [←mul_sub,norm_mul,Real.norm_eq_abs,abs_of_nonneg (φ.nonneg_normed z)]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed z)
      have h := hLip.dist_le_mul (x-z) (y-z)
      simpa only [euclideanProject_sub,dist_sub_right,Real.dist_eq,Real.norm_eq_abs] using h
    _ = (C:ℝ)*dist x y := by rw [integral_mul_const,φ.integral_normed,one_mul]

lemma configurationMollify_approximation (L : Length) (φ : ContDiffBump (0 : EuclideanConfiguration ι))
    {f : (ι→Torus L)→ℝ} (hf : Continuous f) {C : ℝ≥0}
    (hLip : LipschitzWith C (fun x : EuclideanConfiguration ι ↦ f (euclideanProject L x))) (X : ι→Torus L) :
    dist (configurationMollify L φ f X) (f X)≤(C:ℝ)*φ.rOut := by
  obtain ⟨x,rfl⟩ := euclideanProject_surjective L X
  rw [show configurationMollify L φ f (euclideanProject L x)=
    (φ.normed volume ⋆[lsmul ℝ ℝ,volume] (fun y ↦ f (euclideanProject L y))) x from
    congrFun (configurationMollify_lift L φ f) x]
  apply φ.dist_normed_convolution_le (hf.comp (euclideanProject_continuous L)).aestronglyMeasurable
  intro y hy
  exact (hLip.dist_le_mul y x).trans (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy).le C.coe_nonneg)

end HardSphere

end

end OAI
