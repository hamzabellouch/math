import Mathlib
import OAI.Probability.SphericalField.Entropy.StationaryExistence
import OAI.Probability.SphericalField.Sphere.AmplitudeConvex

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron

lemma expectedCoordinateSphereLog_stationary_covariance {k : ℕ} (w h : Fin (k+1) → ℝ)
    (q : Fin (k+1) → Time) (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1)
    (hq : Monotone q) (hq1 : (q (Fin.last k):ℝ) < 1)
    (hstat : ∀ i, 2*h i = weightedStepA w (fun j => (q j:ℝ)) (q i))
    (σ : ℕ → ℝ) (v : ℝ≥0) (hv : (v:ℝ)=2*h 0)
    (hσ : ∀ i : Fin k, (σ (k-1-i.val))^2=2*(h i.succ-h i.castSucc)) :
    Tendsto (fun n : ℕ => expectedCoordinateSphereLog n k σ (stepCumulative w) v-h (Fin.last k)) atTop
      (𝓝 ((entropy (weightedStepTrial w q (fun i => (hw i).le) hw1)).toReal-
        ∑ i, w i*h i*(q i:ℝ))) := by
  let Q : Fin (k+1) → ℝ := fun i => q i
  let D : Fin (k+1) → ℝ := fun i => weightedStepTail w Q (Q i)
  have hm : Monotone Q := fun i j hij => hq hij
  have h0 : 0 ≤ Q 0 := (q 0).2.1
  have hmax (i : Fin (k+1)) : Q i ≤ Q (Fin.last k) := hm (Fin.le_last i)
  have hD (i : Fin (k+1)) : 0 < D i :=
    weightedStepTail_pos w Q (fun i => (hw i).le) hw1 hq1 hmax (hmax i)
  have hz := stepCumulative_strictMono w hw
  have hz0 := stepCumulative_pos w hw
  have hz1 := stepCumulative_lt_one w hw hw1
  have hroot : 2*h 0=Q 0/(D 0)^2 :=
    (hstat 0).trans (weightedStepA_root w Q hm h0)
  have hinc (i : Fin k) : 2*(h i.succ-h i.castSucc)=
      (Q i.succ-Q i.castSucc)/(D i.castSucc*D i.succ) := by
    calc
      _ = weightedStepA w Q (Q i.succ)-weightedStepA w Q (Q i.castSucc) := by
        linarith [hstat i.succ,hstat i.castSucc]
      _ = _ := weightedStepA_increment w Q (fun i => (hw i).le) hw1 hm h0 hq1 i (hz0 i)
  have hr : (v:ℝ)=Q 0/(D 0)^2 := hv.trans hroot
  have hend : D (Fin.last k) = 1-Q (Fin.last k) := weightedStepTail_of_le w Q hw1 hmax
  have hgap (i : Fin k) : D i.castSucc-D i.succ=stepCumulative w i*(Q i.succ-Q i.castSucc) := by
    have he := weightedStepTail_affine w Q hm i (t := Q i.succ) ⟨hm (Fin.castSucc_le_succ i),le_rfl⟩
    change D i.succ=D i.castSucc-stepCumulative w i*(Q i.succ-Q i.castSucc) at he
    linarith
  have hσ' (i : Fin k) : (σ (k-1-i.val))^2=
      (Q i.succ-Q i.castSucc)/(D i.castSucc*D i.succ) := (hσ i).trans (hinc i)
  have ht := (expectedCoordinateSphereLog_stationary_data k σ
    Q D (stepCumulative w) hz hz0 hz1 hD hend hgap hσ' v hr).sub_const (h (Fin.last k))
  have he := entropy_weightedStepTrial_toReal_finite_formula w q (fun i => (hw i).le) hw1 hq hq1 hz0
  simp only [tailIntegral_weightedStepTrial] at he
  change (entropy (weightedStepTrial w q (fun i => (hw i).le) hw1)).toReal =
    Real.log (D (Fin.last k))/2+stepLogRatios k D (stepCumulative w)+Q 0/(2*D 0) at he
  have hs := stationary_field_shift_identity w Q h hw1 hm hD hroot hinc
  have hv : Real.log (D (Fin.last k))/2+stepLogRatios k D (stepCumulative w)+Q 0/(2*D 0)+
      ((D (Fin.last k))⁻¹-1)/2-h (Fin.last k) =
      (entropy (weightedStepTrial w q (fun i => (hw i).le) hw1)).toReal-∑ i, w i*h i*Q i := by
    rw [he]
    change 2*(h (Fin.last k)-∑ i, w i*h i*Q i)=(D (Fin.last k))⁻¹-1 at hs
    linarith
  rw [hv] at ht
  exact ht

def amplitudeCovarianceLevels (k : ℕ) (σ : ℕ → ℝ) (r : ℝ) (i : Fin (k+1)) : ℝ :=
  (r^2+stepTailSum (fun j : Fin k => (σ (k-1-j.val))^2) 0-
    stepTailSum (fun j : Fin k => (σ (k-1-j.val))^2) i)/2

lemma amplitudeCovarianceLevels_root (k : ℕ) (σ : ℕ → ℝ) (r : ℝ) :
    2*amplitudeCovarianceLevels k σ r 0=r^2 := by unfold amplitudeCovarianceLevels; ring

lemma amplitudeCovarianceLevels_increment (k : ℕ) (σ : ℕ → ℝ) (r : ℝ) (i : Fin k) :
    2*(amplitudeCovarianceLevels k σ r i.succ-amplitudeCovarianceLevels k σ r i.castSucc)=
      (σ (k-1-i.val))^2 := by
  have he := stepTailSum_difference (fun j : Fin k => (σ (k-1-j.val))^2) i
  unfold amplitudeCovarianceLevels
  linarith

lemma amplitudeCovarianceLevels_monotone (k : ℕ) (σ : ℕ → ℝ) (r : ℝ) :
    Monotone (amplitudeCovarianceLevels k σ r) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  have h := amplitudeCovarianceLevels_increment k σ r i
  nlinarith [sq_nonneg (σ (k-1-i.val))]

lemma amplitudeCovarianceLevels_nonneg (k : ℕ) (σ : ℕ → ℝ) (r : ℝ) :
    0 ≤ amplitudeCovarianceLevels k σ r 0 := by
  have h := amplitudeCovarianceLevels_root k σ r
  nlinarith [sq_nonneg r]

def amplitudeSphereDual {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1) (σ : ℕ → ℝ) (r : ℝ) : ℝ :=
  sInf (finiteSphericalDualValues w (amplitudeCovarianceLevels k σ r) hw hw1)+
    amplitudeCovarianceLevels k σ r (Fin.last k)

lemma amplitudeSphereValue_tendsto {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) (σ : ℕ → ℝ) (r : ℝ) :
    Tendsto (fun n : ℕ => amplitudeSphereValue n k σ (stepCumulative w) r) atTop
      (𝓝 (amplitudeSphereDual w (fun i => (hw i).le) hw1 σ r)) := by
  let h := amplitudeCovarianceLevels k σ r
  obtain ⟨q,hq,hq1,hs⟩ := exists_finite_stationary_quantile w h hw hw1
    (amplitudeCovarianceLevels_monotone k σ r) (amplitudeCovarianceLevels_nonneg k σ r)
  have hleast : IsLeast (finiteSphericalDualValues w h (fun i => (hw i).le) hw1)
      (finiteSphericalDualObjective w h (fun i => (hw i).le) hw1 q) := by
    refine ⟨⟨q,⟨hq,hq1⟩,rfl⟩,?_⟩
    rintro a ⟨p,⟨hp,hp1⟩,rfl⟩
    exact stationary_finite_entropy_minimizes w h q p (fun i => (hw i).le) hw1 hq hp hq1 hp1 hs
  have ht := (expectedCoordinateSphereLog_stationary_covariance w h q hw hw1 hq hq1 hs σ
    ⟨r^2,sq_nonneg r⟩ (amplitudeCovarianceLevels_root k σ r).symm
    (fun i => (amplitudeCovarianceLevels_increment k σ r i).symm)).add_const (h (Fin.last k))
  simp only [sub_add_cancel,← amplitudeSphereValue_eq] at ht
  change Tendsto _ _ (𝓝 (sInf (finiteSphericalDualValues w h (fun i => (hw i).le) hw1)+h (Fin.last k)))
  rw [hleast.csInf_eq]
  exact ht

def finiteAmplitudeIncrement (k : ℕ) (a : Fin (k+1) → ℝ) (j : ℕ) : ℝ :=
  if hj : j < k then a (⟨j,hj⟩ : Fin k).castSucc else 0

def finiteAmplitudeSphereValue (n k : ℕ) (w : Fin (k+1) → ℝ) (a : Fin (k+1) → ℝ) : ℝ :=
  amplitudeSphereValue n k (finiteAmplitudeIncrement k a) (stepCumulative w) (a (Fin.last k))

def finiteAmplitudeSphereDual {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1) (a : Fin (k+1) → ℝ) : ℝ :=
  amplitudeSphereDual w hw hw1 (finiteAmplitudeIncrement k a) (a (Fin.last k))

lemma finiteAmplitudeSphereValue_convex {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) (n : ℕ) :
    ConvexOn ℝ Set.univ (finiteAmplitudeSphereValue n k w) := by
  refine ⟨convex_univ,?_⟩
  intro a _ b _ c d hc hd hcd
  have he : finiteAmplitudeIncrement k (c • a+d • b)=
      c • finiteAmplitudeIncrement k a+d • finiteAmplitudeIncrement k b := by
    funext j
    unfold finiteAmplitudeIncrement
    by_cases hj : j < k
    · simp [hj,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    · simp [hj,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  simpa only [finiteAmplitudeSphereValue,he,Pi.add_apply,Pi.smul_apply,smul_eq_mul] using
    amplitudeSphereValue_convex n k (stepCumulative w) (stepCumulative_strictMono w hw)
      (stepCumulative_pos w hw) (stepCumulative_lt_one w hw hw1)
      (finiteAmplitudeIncrement k a) (finiteAmplitudeIncrement k b) (a (Fin.last k))
      (b (Fin.last k)) hc hd hcd

lemma finiteAmplitudeSphereValue_nonneg {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) (n : ℕ) (a : Fin (k+1) → ℝ) :
    0 ≤ finiteAmplitudeSphereValue n k w a :=
  integral_nonneg_of_ae (amplitudeSphereLog_nonneg n k _ _ (stepCumulative_strictMono w hw)
    (stepCumulative_pos w hw) (stepCumulative_lt_one w hw hw1) _)

lemma finiteAmplitudeSphereValue_tendsto {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) (a : Fin (k+1) → ℝ) :
    Tendsto (fun n : ℕ => finiteAmplitudeSphereValue n k w a) atTop
      (𝓝 (finiteAmplitudeSphereDual w (fun i => (hw i).le) hw1 a)) :=
  amplitudeSphereValue_tendsto w hw hw1 _ _

end SphericalPerceptron
end
end

end OAI
