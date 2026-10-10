import Mathlib
import OAI.Analysis.HardSphere.Geometry.LocalCloseLabels

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

private def flattenLinear (n : ℕ) : LiftedConfiguration n→ₗ[ℝ] EuclideanConfiguration (Fin n) where
  toFun X := WithLp.toLp 2 (fun p ↦ X p.1 p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def euclideanFlatten (n : ℕ) : LiftedConfiguration n→L[ℝ] EuclideanConfiguration (Fin n) :=
  (flattenLinear n).toContinuousLinearMap

lemma euclideanFlatten_apply (n : ℕ) (X : LiftedConfiguration n) (p : Direction n) :
    euclideanFlatten n X p=X p.1 p.2 := rfl

lemma euclideanFlatten_project (n : ℕ) (L : Length) (X : LiftedConfiguration n) :
    euclideanProject L (euclideanFlatten n X)=project n L X := rfl

lemma euclideanFlatten_single (n : ℕ) (p : Direction n) :
    euclideanFlatten n (Pi.single p.1 (Pi.single p.2 1))=EuclideanSpace.basisFun (Direction n) ℝ p := by
  ext q
  by_cases h1 : q.1=p.1 <;> by_cases h2 : q.2=p.2 <;>
    simp [euclideanFlatten_apply,EuclideanSpace.basisFun_apply,Prod.ext_iff,h1,h2]

lemma realEuclidean_lift_smooth {n : ℕ} (L : Length) (f : Configuration n L→ℝ)
    (hf : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun x : EuclideanConfiguration (Fin n) ↦ f (euclideanProject L x))) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun x : LiftedConfiguration n ↦ (f (project n L x):ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (hf.comp (euclideanFlatten n).contDiff)

def realEuclideanMultiplier {n : ℕ} (L : Length) (f : Configuration n L→ℝ)
    (hf : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun x : EuclideanConfiguration (Fin n) ↦ f (euclideanProject L x))) :
    SmoothMultiplier n L := SmoothMultiplier.ofSmooth (fun X ↦ (f X:ℂ)) (realEuclidean_lift_smooth L f hf)

lemma coordDerivative_real_euclidean {n : ℕ} (L : Length) (f : Configuration n L→ℝ)
    (hf : Differentiable ℝ (fun x : EuclideanConfiguration (Fin n) ↦ f (euclideanProject L x)))
    (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (fun Y ↦ (f Y:ℂ)) p X=
      ((fderiv ℝ (fun x : EuclideanConfiguration (Fin n) ↦ f (euclideanProject L x))
        (euclideanFlatten n (representative n L X)) (EuclideanSpace.basisFun (Direction n) ℝ p)):ℂ) := by
  have hh := (Complex.ofRealCLM.hasFDerivAt.comp _ (hf _).hasFDerivAt).comp
    (representative n L X) (euclideanFlatten n).hasFDerivAt
  have he : ((Complex.ofRealCLM ∘ (fun x : EuclideanConfiguration (Fin n) ↦ f (euclideanProject L x))) ∘ euclideanFlatten n)=
      (fun x : LiftedConfiguration n ↦ (f (project n L x):ℂ)) := by
    funext x
    rfl
  rw [he] at hh
  unfold coordDerivative
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.comp_apply,euclideanFlatten_single,Complex.ofRealCLM_apply]

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

lemma clippedNearest_le (L : Length) (X Y : ι→Torus L) (i k : ι) (t : ℝ)
    (hi : X i=Y i) (hrest : ∀ j, j≠k → X j=Y j)
    (hfar : t≤torusDistance L (Y i) (Y k)) :
    min (nearestParticleDistance L X i) t≤nearestParticleDistance L Y i := by
  by_cases he : nearestLabel L Y i=k
  · simpa only [nearestParticleDistance,he] using (min_le_right (nearestParticleDistance L X i) t).trans hfar
  · have hn := nearestParticleDistance_le L X i (nearestLabel L Y i) (nearestLabel_ne L Y i)
    rw [hi,hrest _ he] at hn
    exact (min_le_left _ _).trans hn

lemma clippedNearest_eq (L : Length) (X Y : ι→Torus L) (i k : ι) (t : ℝ)
    (hi : X i=Y i) (hrest : ∀ j, j≠k → X j=Y j)
    (hXfar : t≤torusDistance L (X i) (X k)) (hYfar : t≤torusDistance L (Y i) (Y k)) :
    min (nearestParticleDistance L X i) t=min (nearestParticleDistance L Y i) t :=
  le_antisymm (le_min (clippedNearest_le L X Y i k t hi hrest hYfar) (min_le_right _ _))
    (le_min (clippedNearest_le L Y X i k t hi.symm (fun j h ↦ (hrest j h).symm) hXfar) (min_le_right _ _))

lemma closeRamp_clipped {s d : ℝ} (hs : 0<s) :
    closeRamp (2-d/s)=closeRamp (2-min d (2*s)/s) := by
  by_cases h : d≤2*s
  · rw [min_eq_left h]
  · rw [min_eq_right (le_of_not_ge h)]
    have hd : 2≤d/s := (le_div_iff₀ hs).mpr (le_of_not_ge h)
    rw [closeRamp_zero (t:=2-d/s) (by linarith only [hd])]
    have he : 2-2*s/s=0 := by field_simp; ring
    rw [he,closeRamp_zero le_rfl]

lemma far_from_near_separated (L : Length) (a b v : Torus L) (hnear : torusDistance L a v<6)
    (hfar : 7≤torusDistance L b v) : 1≤torusDistance L a b := by
  have ht := torusDistance_triangle' L b a v
  have he : torusDistance L b a=torusDistance L a b := by simp only [torusDistance,dist_comm]
  rw [he] at ht
  linarith only [hnear,hfar,ht]

theorem closeAmplitude_away_eq (L : Length) {s : ℝ} (hs : 0<s) (hs1 : 2*s≤1)
    (v : Torus L) (X Y : ι→Torus L) (k : ι) (hrest : ∀ i, i≠k → X i=Y i)
    (hXfar : 7≤torusDistance L (X k) v) (hYfar : 7≤torusDistance L (Y k) v) (i : ι) :
    closeAmplitude L s v X i=closeAmplitude L s v Y i := by
  by_cases hik : i=k
  · subst i
    rw [closeAmplitude_zero_of_far L s v X k (by linarith only [hXfar]),
      closeAmplitude_zero_of_far L s v Y k (by linarith only [hYfar])]
  · have hi := hrest i hik
    by_cases hv : torusDistance L (X i) v<6
    · have hxf := hs1.trans (far_from_near_separated L (X i) (X k) v hv hXfar)
      have hyv : torusDistance L (Y i) v<6 := hi ▸ hv
      have hyf := hs1.trans (far_from_near_separated L (Y i) (Y k) v hyv hYfar)
      have he := clippedNearest_eq L X Y i k (2*s) hi hrest hxf hyf
      unfold closeAmplitude
      rw [hi,closeRamp_clipped (d:=nearestParticleDistance L X i) hs,
        closeRamp_clipped (d:=nearestParticleDistance L Y i) hs,he]
    · have hxv : 6≤torusDistance L (X i) v := le_of_not_gt hv
      have hyv : 6≤torusDistance L (Y i) v := hi ▸ hxv
      rw [closeAmplitude_zero_of_far L s v X i hxv,closeAmplitude_zero_of_far L s v Y i hyv]

lemma localCloseSmoothCount_away_eq (L : Length) {s : ℝ} (hs : 0<s) (hs1 : 2*s≤1)
    (v : Torus L) (X Y : ι→Torus L) (k : ι) (hrest : ∀ i, i≠k → X i=Y i)
    (hXfar : 7≤torusDistance L (X k) v) (hYfar : 7≤torusDistance L (Y k) v) :
    localCloseSmoothCount L s v X=localCloseSmoothCount L s v Y := by
  apply Finset.sum_congr rfl
  intro i _
  rw [closeAmplitude_away_eq L hs hs1 v X Y k hrest hXfar hYfar i]

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
open scoped Convolution NNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

def mollifiedCloseRoot (L : Length) (s : ℝ) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration ι)) : (ι→Torus L)→ℝ :=
  configurationMollify L φ (localCloseRoot L s v)

def mollifiedCloseCount (L : Length) (s : ℝ) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration ι)) (X : ι→Torus L) : ℝ :=
  mollifiedCloseRoot L s v φ X^2

lemma mollifiedCloseRoot_nonneg (L : Length) (s : ℝ) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration ι)) (X : ι→Torus L) :
    0 ≤ mollifiedCloseRoot L s v φ X :=
  configurationMollify_nonneg L φ _ (fun _ ↦ norm_nonneg _) X

lemma mollifiedCloseRoot_smooth (L : Length) (s : ℝ) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration ι)) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun x : EuclideanConfiguration ι ↦ mollifiedCloseRoot L s v φ (euclideanProject L x)) :=
  configurationMollify_smooth L φ _ (localCloseRoot_continuous L s v)

lemma mollifiedCloseCount_smooth (L : Length) (s : ℝ) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration ι)) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun x : EuclideanConfiguration ι ↦ mollifiedCloseCount L s v φ (euclideanProject L x)) :=
  (mollifiedCloseRoot_smooth L s v φ).pow 2

lemma mollifiedCloseRoot_lipschitz (L : Length) {s : ℝ} (hs : 0<s) (hs1 : s≤1) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration ι)) :
    LipschitzWith ⟨32/s,by positivity⟩ (fun x : EuclideanConfiguration ι ↦ mollifiedCloseRoot L s v φ (euclideanProject L x)) :=
  configurationMollify_lipschitz L φ (localCloseRoot_continuous L s v)
    (localCloseRoot_euclidean_lipschitz L hs hs1 v)

lemma mollifiedCloseRoot_approximation (L : Length) {s : ℝ} (hs : 0<s) (hs1 : s≤1) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration ι)) (X : ι→Torus L) :
    |mollifiedCloseRoot L s v φ X-localCloseRoot L s v X|≤(32/s)*φ.rOut := by
  exact configurationMollify_approximation L φ (localCloseRoot_continuous L s v)
    (localCloseRoot_euclidean_lipschitz L hs hs1 v) X

lemma self_gradient_square_of_lipschitz {κ : Type*} [Fintype κ] {C : ℝ≥0}
    {f : EuclideanSpace ℝ κ→ℝ} (hf : LipschitzWith C f) {x : EuclideanSpace ℝ κ}
    (hx : DifferentiableAt ℝ f x) :
      (∑ p, (fderiv ℝ (fun y ↦ f y^2) x (EuclideanSpace.basisFun κ ℝ p))^2)≤
        (4*(C:ℝ)^2)*f x^2 := by
  rw [←(EuclideanSpace.basisFun κ ℝ).norm_dual,fderiv_fun_pow 2 hx]
  simp only [Nat.reduceSub,pow_one,nsmul_eq_mul,Nat.cast_ofNat,norm_smul,Real.norm_eq_abs]
  have hb := norm_fderiv_le_of_lipschitz ℝ (x₀:=x) hf
  have hsq := (sq_le_sq₀ (norm_nonneg _) C.coe_nonneg).mpr hb
  calc
    _ = (4*f x^2)*‖fderiv ℝ f x‖^2 := by rw [mul_pow,sq_abs]; ring
    _ ≤ (4*f x^2)*(C:ℝ)^2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by ring

lemma mollifiedCloseCount_gradient (L : Length) {s : ℝ} (hs : 0<s) (hs1 : s≤1) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration ι)) (x : EuclideanConfiguration ι) :
      (∑ p, (fderiv ℝ (fun y ↦ mollifiedCloseCount L s v φ (euclideanProject L y)) x
        (EuclideanSpace.basisFun (ι×Fin 3) ℝ p))^2)≤
          (4096/s^2)*mollifiedCloseCount L s v φ (euclideanProject L x) := by
  have h := self_gradient_square_of_lipschitz (mollifiedCloseRoot_lipschitz L hs hs1 v φ)
    ((mollifiedCloseRoot_smooth L s v φ).differentiable (by simp) x)
  have hc : (4:ℝ)*(32/s)^2=4096/s^2 := by ring
  rw [←hc]
  exact h

end HardSphere

end

end OAI
