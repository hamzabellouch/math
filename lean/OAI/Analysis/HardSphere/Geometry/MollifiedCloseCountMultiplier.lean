import Mathlib
import OAI.Analysis.HardSphere.Geometry.FlattenLinear

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
open scoped ComplexConjugate
variable {n : ℕ} [Nontrivial (Fin n)]

def mollifiedCloseCountMultiplier (L : Length) (s : ℝ) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) : SmoothMultiplier n L :=
  realEuclideanMultiplier L (mollifiedCloseCount L s v φ) (mollifiedCloseCount_smooth L s v φ)

lemma mollifiedCloseCountMultiplier_apply (L : Length) (s : ℝ) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (X : Configuration n L) :
    (mollifiedCloseCountMultiplier L s v φ).toFun X=(mollifiedCloseCount L s v φ X:ℂ) := rfl

lemma mollifiedCloseCountMultiplier_real (L : Length) (s : ℝ) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (X : Configuration n L) :
    conj ((mollifiedCloseCountMultiplier L s v φ).toFun X)=(mollifiedCloseCountMultiplier L s v φ).toFun X :=
  Complex.conj_ofReal _

lemma mollifiedCloseCountMultiplier_gradient (L : Length) {s : ℝ} (hs : 0<s) (hs1 : s≤1) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (X : Configuration n L) :
    (∑ p : Direction n, ‖coordDerivative n L (mollifiedCloseCountMultiplier L s v φ).toFun p X‖^2)≤
      (4096/s^2)*mollifiedCloseCount L s v φ X := by
  change (∑ p : Direction n, ‖coordDerivative n L (fun Y ↦ (mollifiedCloseCount L s v φ Y:ℂ)) p X‖^2)≤_
  simp_rw [coordDerivative_real_euclidean L _
    ((mollifiedCloseCount_smooth L s v φ).differentiable (by simp)),
    Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have h := mollifiedCloseCount_gradient L hs hs1 v φ (euclideanFlatten n (representative n L X))
  simpa only [euclideanFlatten_project,project_representative] using h

def closeHighProfile (h t : ℝ) : ℝ := 1-CellOrbital.profile h t

lemma closeHighProfile_smooth (h : ℝ) : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (closeHighProfile h) :=
  contDiff_const.sub (CellOrbital.profile_smooth h)

lemma closeHighProfile_bounds (h t : ℝ) : 0≤closeHighProfile h t ∧ closeHighProfile h t≤1 := by
  have h := CellOrbital.profile_bounds h t
  unfold closeHighProfile
  constructor <;> linarith only [h.1,h.2]

lemma closeHighProfile_zero {h : ℝ} (hh : 0<h) {t : ℝ} (ht : t≤h) : closeHighProfile h t=0 := by
  rw [closeHighProfile,CellOrbital.profile_one hh ht,sub_self]
lemma closeHighProfile_one {h : ℝ} (hh : 0<h) {t : ℝ} (ht : 2*h≤t) : closeHighProfile h t=1 := by
  rw [closeHighProfile,CellOrbital.profile_zero hh ht,sub_zero]

lemma closeHighProfile_deriv (h t : ℝ) : deriv (closeHighProfile h) t= -deriv (CellOrbital.profile h) t := by
  exact ((CellOrbital.profile_smooth h).differentiable (by simp) t).hasDerivAt.const_sub 1 |>.deriv

lemma closeHighProfile_deriv_zero {h : ℝ} (hh : 0<h) {t : ℝ} (ht : t∉Icc h (2*h)) :
    deriv (closeHighProfile h) t=0 := by
  rw [closeHighProfile_deriv,CellOrbital.profile_deriv_zero hh ht,neg_zero]

lemma closeHighProfile_deriv_bound {h M : ℝ} (hh : 0<h) (hM : 0≤M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M) (t : ℝ) :
    |deriv (closeHighProfile h) t|≤M/h := by
  rw [closeHighProfile_deriv,abs_neg]
  exact CellOrbital.profile_deriv_bound hh hM hb t

def mollifiedCloseCutoff (L : Length) (s : ℝ) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (h : ℝ) : SmoothMultiplier n L :=
  (mollifiedCloseCountMultiplier L s v φ).realComp (closeHighProfile h) (closeHighProfile_smooth h)

lemma mollifiedCloseCutoff_apply (L : Length) (s : ℝ) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (h : ℝ) (X : Configuration n L) :
    (mollifiedCloseCutoff L s v φ h).toFun X=(closeHighProfile h (mollifiedCloseCount L s v φ X):ℂ) := by
  change (closeHighProfile h ((mollifiedCloseCountMultiplier L s v φ).toFun X).re:ℂ)=_
  rw [mollifiedCloseCountMultiplier_apply,Complex.ofReal_re]

lemma mollifiedCloseCutoff_partial (L : Length) (s : ℝ) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (h : ℝ) (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (mollifiedCloseCutoff L s v φ h).toFun p X=
      ((deriv (closeHighProfile h) (mollifiedCloseCount L s v φ X):ℝ):ℂ)*
        coordDerivative n L (mollifiedCloseCountMultiplier L s v φ).toFun p X := by
  rw [mollifiedCloseCutoff,SmoothMultiplier.partial_realComp _ _ _ (mollifiedCloseCountMultiplier_real L s v φ),
    mollifiedCloseCountMultiplier_apply,Complex.ofReal_re]

theorem mollifiedCloseCutoff_gradient (L : Length) {s h M : ℝ} (hs : 0<s) (hs1 : s≤1)
    (hh : 0<h) (hM : 0≤M) (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M)
    (v : Torus L) (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (X : Configuration n L) :
    (∑ p : Direction n, ‖coordDerivative n L (mollifiedCloseCutoff L s v φ h).toFun p X‖^2)≤
      8192*M^2/(h*s^2) := by
  by_cases ht : mollifiedCloseCount L s v φ X∈Icc h (2*h)
  · simp_rw [mollifiedCloseCutoff_partial,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    rw [←Finset.mul_sum]
    have hb2 : (deriv (closeHighProfile h) (mollifiedCloseCount L s v φ X))^2≤(M/h)^2 := by
      rw [←sq_abs (deriv _ _)]
      exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (closeHighProfile_deriv_bound hh hM hb _)
    calc
      _ ≤ (M/h)^2*((4096/s^2)*mollifiedCloseCount L s v φ X) :=
        mul_le_mul hb2 (mollifiedCloseCountMultiplier_gradient L hs hs1 v φ X)
          (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (by positivity)
      _ ≤ (M/h)^2*((4096/s^2)*(2*h)) := by
        gcongr
        exact ht.2
      _ = _ := by field_simp; ring
  · simp_rw [mollifiedCloseCutoff_partial,closeHighProfile_deriv_zero hh ht,Complex.ofReal_zero,zero_mul,
      norm_zero,zero_pow (by norm_num : 2≠0),Finset.sum_const_zero]
    positivity

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma euclideanProject_move_one_le (L : Length) (X : ι→Torus L)
    (y : EuclideanConfiguration ι) (k : ι) :
    torusDistance L (X k) ((X-euclideanProject L y) k)≤‖y‖ := by
  obtain ⟨x,rfl⟩ := euclideanProject_surjective L X
  have hsingle := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun i ↦ torusDistance L (euclideanProject L x i) (euclideanProject L (x-y) i)^2)
    (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ k)
  have h := hsingle.trans (euclideanProject_total_sq L x (x-y))
  simp only [euclideanProject_sub,dist_eq_norm,sub_sub_cancel] at h
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) (norm_nonneg y)).mp h

variable [Nontrivial ι]

lemma localCloseRoot_away_eq (L : Length) {s : ℝ} (hs : 0<s) (hs1 : 2*s≤1)
    (v : Torus L) (X Y : ι→Torus L) (k : ι) (hrest : ∀ i, i≠k → X i=Y i)
    (hXfar : 7≤torusDistance L (X k) v) (hYfar : 7≤torusDistance L (Y k) v) :
    localCloseRoot L s v X=localCloseRoot L s v Y := by
  apply (sq_eq_sq₀ (show 0≤localCloseRoot L s v X from norm_nonneg _)
    (show 0≤localCloseRoot L s v Y from norm_nonneg _)).mp
  rw [localCloseRoot_sq,localCloseRoot_sq,localCloseSmoothCount_away_eq L hs hs1 v X Y k hrest hXfar hYfar]

lemma mollifiedCloseRoot_away_eq (L : Length) {s : ℝ} (hs : 0<s) (hs1 : 2*s≤1)
    (v : Torus L) (φ : ContDiffBump (0 : EuclideanConfiguration ι)) (hφ : φ.rOut≤1)
    (X Y : ι→Torus L) (k : ι) (hrest : ∀ i, i≠k → X i=Y i)
    (hXfar : 8≤torusDistance L (X k) v) (hYfar : 8≤torusDistance L (Y k) v) :
    mollifiedCloseRoot L s v φ X=mollifiedCloseRoot L s v φ Y := by
  unfold mollifiedCloseRoot configurationMollify
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  by_cases hy : φ.normed volume y=0
  · simp only [hy,zero_mul]
  · have hyball : y∈Metric.ball (0 : EuclideanConfiguration ι) φ.rOut := by
      rw [←φ.support_normed_eq (μ:=volume)]
      exact hy
    have hyn : ‖y‖≤1 := (by simpa only [Metric.mem_ball,dist_zero_right] using hyball : ‖y‖<φ.rOut).le.trans hφ
    have hfar (Z : ι→Torus L) (hz : 8≤torusDistance L (Z k) v) :
        7≤torusDistance L ((Z-euclideanProject L y) k) v := by
      have ht := torusDistance_triangle' L (Z k) ((Z-euclideanProject L y) k) v
      have hm := (euclideanProject_move_one_le L Z y k).trans hyn
      linarith only [ht,hm,hz]
    rw [localCloseRoot_away_eq L hs hs1 v (X-euclideanProject L y) (Y-euclideanProject L y) k
      (fun i hi ↦ by simp only [Pi.sub_apply,hrest i hi]) (hfar X hXfar) (hfar Y hYfar)]

lemma mollifiedCloseCount_away_eq (L : Length) {s : ℝ} (hs : 0<s) (hs1 : 2*s≤1)
    (v : Torus L) (φ : ContDiffBump (0 : EuclideanConfiguration ι)) (hφ : φ.rOut≤1)
    (X Y : ι→Torus L) (k : ι) (hrest : ∀ i, i≠k → X i=Y i)
    (hXfar : 8≤torusDistance L (X k) v) (hYfar : 8≤torusDistance L (Y k) v) :
    mollifiedCloseCount L s v φ X=mollifiedCloseCount L s v φ Y := by
  unfold mollifiedCloseCount
  rw [mollifiedCloseRoot_away_eq L hs hs1 v φ hφ X Y k hrest hXfar hYfar]

end HardSphere

end

end OAI
