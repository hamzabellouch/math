import Mathlib
import OAI.Probability.SphericalField.Sphere.AmplitudeLimit
import OAI.Probability.SphericalField.Sphere.ConvexUniform

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron

lemma finiteAmplitudeSphereValue_uniform {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) {K : Set (Fin (k+1) → ℝ)}
    (hK : IsCompact K) : TendstoUniformlyOn (fun n => finiteAmplitudeSphereValue n k w)
      (finiteAmplitudeSphereDual w (fun i => (hw i).le) hw1) atTop K :=
  tendstoUniformlyOn_of_convex_nonneg_tendsto _ _ (finiteAmplitudeSphereValue_convex w hw hw1)
    (finiteAmplitudeSphereValue_nonneg w hw hw1) (finiteAmplitudeSphereValue_tendsto w hw hw1) hK

def fieldAmplitudes (k : ℕ) (h : Fin (k+1) → ℝ) (i : Fin (k+1)) : ℝ :=
  if i.val < k then stepFieldIncrement k h i.val else Real.sqrt (2*h 0)

lemma fieldAmplitudes_last (k : ℕ) (h : Fin (k+1) → ℝ) :
    fieldAmplitudes k h (Fin.last k)=Real.sqrt (2*h 0) := by
  simp [fieldAmplitudes]

lemma fieldAmplitudes_increment (k : ℕ) (h : Fin (k+1) → ℝ) :
    finiteAmplitudeIncrement k (fieldAmplitudes k h)=stepFieldIncrement k h := by
  funext j
  by_cases hj : j < k
  · simp [finiteAmplitudeIncrement,fieldAmplitudes,hj]
  · simp [finiteAmplitudeIncrement,stepFieldIncrement,hj]

lemma fieldAmplitudes_continuous (k : ℕ) : Continuous (fieldAmplitudes k) := by
  apply continuous_pi
  intro i
  unfold fieldAmplitudes
  split_ifs
  · unfold stepFieldIncrement
    split_ifs; fun_prop
  · fun_prop

lemma amplitudeCovarianceLevels_fieldAmplitudes (k : ℕ) (h : Fin (k+1) → ℝ)
    (hh : Monotone h) (hh0 : 0 ≤ h 0) :
    amplitudeCovarianceLevels k (finiteAmplitudeIncrement k (fieldAmplitudes k h))
      (fieldAmplitudes k h (Fin.last k))=h := by
  rw [fieldAmplitudes_increment,fieldAmplitudes_last]
  funext i
  induction i using Fin.induction with
  | zero =>
    have hr := amplitudeCovarianceLevels_root k (stepFieldIncrement k h) (Real.sqrt (2*h 0))
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) hh0)] at hr
    linarith
  | succ i ih =>
    have hi := amplitudeCovarianceLevels_increment k (stepFieldIncrement k h) (Real.sqrt (2*h 0)) i
    rw [stepFieldIncrement_sq k h hh i,ih] at hi
    linarith

lemma finiteAmplitudeSphereDual_fieldAmplitudes {k : ℕ} (w h : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1) (hh : Monotone h) (hh0 : 0 ≤ h 0) :
    finiteAmplitudeSphereDual w hw hw1 (fieldAmplitudes k h)=
      sInf (finiteSphericalDualValues w h hw hw1)+h (Fin.last k) := by
  unfold finiteAmplitudeSphereDual amplitudeSphereDual
  rw [amplitudeCovarianceLevels_fieldAmplitudes k h hh hh0]

lemma finiteAmplitudeSphereValue_fieldAmplitudes (n k : ℕ) (w h : Fin (k+1) → ℝ)
    (hh0 : 0 ≤ h 0) :
    finiteAmplitudeSphereValue n k w (fieldAmplitudes k h)=finiteSphericalFieldValue n k w h+h (Fin.last k) := by
  unfold finiteAmplitudeSphereValue
  rw [fieldAmplitudes_increment,fieldAmplitudes_last,amplitudeSphereValue_eq]
  have hv : (⟨(Real.sqrt (2*h 0))^2,sq_nonneg _⟩ : ℝ≥0)=Real.toNNReal (2*h 0) := by
    apply NNReal.coe_injective
    change (Real.sqrt (2*h 0))^2=(Real.toNNReal (2*h 0) : ℝ)
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) hh0),
      Real.coe_toNNReal _ (mul_nonneg (by norm_num) hh0)]
  rw [hv,finiteSphericalFieldValue,sub_add_cancel]

theorem finiteSphericalFieldValue_compact_uniform {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) {K : Set (Fin (k+1) → ℝ)}
    (hK : IsCompact K) (hfield : ∀ h ∈ K, Monotone h ∧ 0 ≤ h 0) :
    TendstoUniformlyOn (fun n h => finiteSphericalFieldValue n k w h)
      (fun h => sInf (finiteSphericalDualValues w h (fun i => (hw i).le) hw1)) atTop K := by
  have hu := finiteAmplitudeSphereValue_uniform w hw hw1 (hK.image (fieldAmplitudes_continuous k))
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro ε hε
  filter_upwards [hu ε hε] with n hn h hh
  have ht := hn (fieldAmplitudes k h) ⟨h,hh,rfl⟩
  rw [finiteAmplitudeSphereValue_fieldAmplitudes n k w h (hfield h hh).2,
    finiteAmplitudeSphereDual_fieldAmplitudes w h (fun i => (hw i).le) hw1
      (hfield h hh).1 (hfield h hh).2,dist_add_right] at ht
  exact ht

end SphericalPerceptron
end
end

end OAI
