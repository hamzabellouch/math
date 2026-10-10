import Mathlib
import OAI.Analysis.HardSphere.FormDomain.CoordDerivativeParticleLocality

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section
variable {n : ℕ} [Nontrivial (Fin n)]

lemma mollifiedCloseCutoff_partials_disjoint (L : Length) {s : ℝ} (hs : 0<s) (hs1 : 2*s≤1)
    (v w : Torus L) (hvw : 20≤torusDistance L v w)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (hφ : φ.rOut≤1)
    (h : ℝ) (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (mollifiedCloseCutoff L s v φ h).toFun p X=0 ∨
    coordDerivative n L (mollifiedCloseCutoff L s w φ h).toFun p X=0 := by
  by_cases hv : 8<torusDistance L (X p.1) v
  · exact Or.inl (mollifiedCloseCutoff_partial_zero L hs hs1 v φ hφ h p X hv)
  · apply Or.inr
    apply mollifiedCloseCutoff_partial_zero L hs hs1 w φ hφ h p X
    have ht := torusDistance_triangle' L v (X p.1) w
    rw [torusDistance_comm L v (X p.1)] at ht
    linarith only [ht,hvw,le_of_not_gt hv]

def mollifiedCloseJoint (L : Length) (s : ℝ)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (h : ℝ) (A : Finset (Torus L)) : SmoothMultiplier n L := by
  classical
  exact SmoothMultiplier.finsetProd A (fun v ↦ mollifiedCloseCutoff L s v φ h)

lemma mollifiedCloseJoint_apply (L : Length) (s : ℝ)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (h : ℝ) (A : Finset (Torus L)) (X : Configuration n L) :
    (mollifiedCloseJoint L s φ h A).toFun X=∏ v∈A, (closeHighProfile h (mollifiedCloseCount L s v φ X):ℂ) := by
  change (∏ v∈A, (mollifiedCloseCutoff L s v φ h).toFun X)=_
  simp_rw [mollifiedCloseCutoff_apply]

lemma mollifiedCloseJoint_real (L : Length) (s : ℝ)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (h : ℝ) (A : Finset (Torus L)) (X : Configuration n L) :
    conj ((mollifiedCloseJoint L s φ h A).toFun X)=(mollifiedCloseJoint L s φ h A).toFun X := by
  simp only [mollifiedCloseJoint_apply,map_prod,Complex.conj_ofReal]

lemma mollifiedCloseJoint_partial (L : Length) (s : ℝ)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (h : ℝ) (A : Finset (Torus L))
    (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (mollifiedCloseJoint L s φ h A).toFun p X=
      ∑ v∈A, (mollifiedCloseJoint L s φ h (A.erase v)).toFun X*
        coordDerivative n L (mollifiedCloseCutoff L s v φ h).toFun p X := by
  classical
  exact SmoothMultiplier.partial_finsetProd A _ p X

theorem mollifiedCloseJoint_gradient (L : Length) {s h M : ℝ} (hs : 0<s) (hs1 : 2*s≤1)
    (hh : 0<h) (hM : 0≤M) (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (hφ : φ.rOut≤1)
    (A : Finset (Torus L)) (hA : ∀ v∈A, ∀ w∈A, v≠w → 20≤torusDistance L v w) (X : Configuration n L) :
    (∑ p : Direction n, ‖coordDerivative n L (mollifiedCloseJoint L s φ h A).toFun p X‖^2)≤
      (8192*M^2/(h*s^2))*∑ v∈A, ‖(mollifiedCloseJoint L s φ h (A.erase v)).toFun X‖^2 := by
  classical
  have he (p : Direction n) :
      ‖coordDerivative n L (mollifiedCloseJoint L s φ h A).toFun p X‖^2=
        ∑ v∈A, ‖(mollifiedCloseJoint L s φ h (A.erase v)).toFun X‖^2*
          ‖coordDerivative n L (mollifiedCloseCutoff L s v φ h).toFun p X‖^2 := by
    rw [mollifiedCloseJoint_partial,norm_sq_sum_of_disjoint]
    · simp_rw [norm_mul,mul_pow]
    · intro v hv w hw hvw
      rcases mollifiedCloseCutoff_partials_disjoint L hs hs1 v w (hA v hv w hw hvw) φ hφ h p X with h1 | h2
      · exact Or.inl (by rw [h1,mul_zero])
      · exact Or.inr (by rw [h2,mul_zero])
  simp_rw [he]
  rw [Finset.sum_comm]
  simp_rw [←Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  calc
    _ ≤ ‖(mollifiedCloseJoint L s φ h (A.erase v)).toFun X‖^2*(8192*M^2/(h*s^2)) :=
      mul_le_mul_of_nonneg_left (mollifiedCloseCutoff_gradient L hs (by linarith only [hs1,hs]) hh hM hb v φ X) (sq_nonneg _)
    _ = _ := mul_comm _ _

end
end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section
variable {n : ℕ} [Nontrivial (Fin n)]

lemma closeCount_mollified_comparison (L : Length) {s : ℝ} (hs : 0<s) (hs1 : s≤1)
    (v : Torus L) (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (X : Configuration n L) :
    mollifiedCloseCount L s v φ X≤2*localCloseSmoothCount L s v X+2*((32/s)*φ.rOut)^2 ∧
    localCloseSmoothCount L s v X≤2*mollifiedCloseCount L s v φ X+2*((32/s)*φ.rOut)^2 := by
  have he := mollifiedCloseRoot_approximation L hs hs1 v φ X
  have hr : 0≤localCloseRoot L s v X := norm_nonneg _
  have hm := mollifiedCloseRoot_nonneg L s v φ X
  have h1 : |mollifiedCloseRoot L s v φ X|≤localCloseRoot L s v X+(32/s)*φ.rOut := by
    rw [abs_of_nonneg hm]
    have hu := (le_abs_self _).trans he
    linarith only [hu]
  have h2 : |localCloseRoot L s v X|≤ mollifiedCloseRoot L s v φ X+(32/s)*φ.rOut := by
    rw [abs_of_nonneg hr]
    have hu := (neg_le_abs _).trans he
    linarith only [hu]
  have hh1 := sq_le_twice_sq_of_abs_le h1
  have hh2 := sq_le_twice_sq_of_abs_le h2
  rw [localCloseRoot_sq] at hh1 hh2
  exact ⟨hh1,hh2⟩

lemma mollifiedCloseCutoff_nonzero_count (L : Length) {s h : ℝ} (hs : 0<s) (hs1 : s≤1) (hh : 0<h)
    (v : Torus L) (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n)))
    (hφ : ((32/s)*φ.rOut)^2≤h/4) (X : Configuration n L)
    (hn : (mollifiedCloseCutoff L s v φ h).toFun X≠0) :
    h/4≤localCloseSmoothCount L s v X := by
  have hm : h< mollifiedCloseCount L s v φ X := by
    by_contra hle
    have hz := closeHighProfile_zero hh (le_of_not_gt hle)
    rw [mollifiedCloseCutoff_apply,hz,Complex.ofReal_zero] at hn
    exact hn rfl
  have he := (closeCount_mollified_comparison L hs hs1 v φ X).1
  linarith only [hm,he,hφ]

lemma mollifiedCloseCutoff_covers (L : Length) {s h : ℝ} (hs : 0<s) (hs1 : s≤1) (hh : 0<h)
    (v : Torus L) (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n)))
    (hφ : ((32/s)*φ.rOut)^2≤h/4) (X : Configuration n L)
    (hn : 8*h≤((localCloseLabels L s v X).card:ℝ)) :
    (mollifiedCloseCutoff L s v φ h).toFun X=1 := by
  have hm := hn.trans (localCloseSmoothCount_covers L hs v X)
  have he := (closeCount_mollified_comparison L hs hs1 v φ X).2
  have ht : 2*h≤ mollifiedCloseCount L s v φ X := by linarith only [hm,he,hφ,hh]
  rw [mollifiedCloseCutoff_apply,closeHighProfile_one hh ht,Complex.ofReal_one]

lemma mollifiedCloseJoint_covers (L : Length) {s h : ℝ} (hs : 0<s) (hs1 : s≤1) (hh : 0<h)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (hφ : ((32/s)*φ.rOut)^2≤h/4)
    (A : Finset (Torus L)) (X : Configuration n L)
    (hclose : ∀ v∈A, 8*h≤((localCloseLabels L s v X).card:ℝ)) :
    (mollifiedCloseJoint L s φ h A).toFun X=1 := by
  change (∏ v∈A, (mollifiedCloseCutoff L s v φ h).toFun X)=1
  exact Finset.prod_eq_one (fun v hv ↦ mollifiedCloseCutoff_covers L hs hs1 hh v φ hφ X (hclose v hv))

lemma mollifiedCloseJoint_nonzero_count (L : Length) {s h : ℝ} (hs : 0<s) (hs1 : s≤1) (hh : 0<h)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (hφ : ((32/s)*φ.rOut)^2≤h/4)
    (A : Finset (Torus L)) (hA : ∀ v∈A, ∀ w∈A, v≠w → 20≤torusDistance L v w)
    (X : Configuration n L) (hne : (mollifiedCloseJoint L s φ h A).toFun X≠0) :
    (h/4)*(A.card:ℝ)≤((localizedNearLabels L A s X).card:ℝ) := by
  classical
  have hn : ∀ v∈A, (mollifiedCloseCutoff L s v φ h).toFun X≠0 := Finset.prod_ne_zero_iff.mp hne
  calc
    _ = ∑ _v∈A, h/4 := by simp [mul_comm]
    _ ≤ ∑ v∈A, localCloseSmoothCount L s v X :=
      Finset.sum_le_sum (fun v hv ↦ mollifiedCloseCutoff_nonzero_count L hs hs1 hh v φ hφ X (hn v hv))
    _ ≤ _ := localCloseSmoothCount_sum_le L hs A (fun v hv w hw hvw ↦ lt_of_lt_of_le (by norm_num : (12:ℝ)<20) (hA v hv w hw hvw)) X

omit [Nontrivial (Fin n)] in
lemma exists_close_mollifier (s h : ℝ) (hs : 0<s) (hh : 0<h) :
    ∃ φ : ContDiffBump (0 : EuclideanConfiguration (Fin n)), φ.rOut≤1 ∧ ((32/s)*φ.rOut)^2≤h/4 := by
  let δ : ℝ := min (1/2) (s*Real.sqrt h/128)
  have hδ : 0<δ := lt_min (by norm_num) (by positivity)
  let φ : ContDiffBump (0 : EuclideanConfiguration (Fin n)) := ⟨δ/2,δ,by positivity,by linarith only [hδ]⟩
  refine ⟨φ, (min_le_left _ _).trans (by norm_num),?_⟩
  have he : (32/s)*φ.rOut≤Real.sqrt h/4 := by
    change (32/s)*δ≤_
    calc
      _ ≤ (32/s)*(s*Real.sqrt h/128) := mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = _ := by field_simp; ring
  have he' := (sq_le_sq₀ (mul_nonneg (by positivity) φ.rOut_pos.le) (by positivity)).mpr he
  have hhroot := Real.sq_sqrt hh.le
  nlinarith only [he',hhroot,hh]

end
end HardSphere

end
end
end
end
end
end
end
end

end OAI
