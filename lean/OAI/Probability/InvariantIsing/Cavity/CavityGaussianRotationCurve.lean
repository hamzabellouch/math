import OAI.Probability.InvariantIsing.Cavity.CavityGaussianPenalty

namespace OAI

/-! The trigonometric interpolation between independent Gaussian fields,
with the cavity-size penalty removed along the same path. -/

noncomputable section
open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def cavityGaussianCurve {X : Type*} {d : ℕ}
    (C A : X → Fin d → ℝ) (t : ℝ) : X → Fin d → ℝ :=
  fun x i => Real.cos t * C x i + Real.sin t * A x i

def cavityGaussianCurveDerivative {X : Type*} {d : ℕ}
    (C A : X → Fin d → ℝ) (t : ℝ) : X → Fin d → ℝ :=
  fun x i => -Real.sin t * C x i + Real.cos t * A x i

def cavityPenaltyCurve {X : Type*} (H V : X → ℝ) (c t : ℝ) : X → ℝ :=
  fun x => H x - 2 * c * Real.cos t ^ 2 * V x

lemma cavityGaussianCurve_linear {X : Type*} {d : ℕ}
    (C A : X → Fin d → ℝ) (t : ℝ) (g : Fin d → ℝ) (x : X) :
    linearGaussian (cavityGaussianCurve C A t) g x =
      Real.cos t * linearGaussian C g x + Real.sin t * linearGaussian A g x := by
  simp only [linearGaussian, cavityGaussianCurve, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

lemma cavityGaussianCurveDerivative_linear {X : Type*} {d : ℕ}
    (C A : X → Fin d → ℝ) (t : ℝ) (g : Fin d → ℝ) (x : X) :
    linearGaussian (cavityGaussianCurveDerivative C A t) g x =
      -Real.sin t * linearGaussian C g x + Real.cos t * linearGaussian A g x := by
  simp only [linearGaussian, cavityGaussianCurveDerivative, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

lemma cavityGaussianCurve_hasDerivAt {X : Type*} {d : ℕ}
    (C A : X → Fin d → ℝ) (t : ℝ) (g : Fin d → ℝ) (x : X) :
    HasDerivAt (fun s => linearGaussian (cavityGaussianCurve C A s) g x)
      (linearGaussian (cavityGaussianCurveDerivative C A t) g x) t := by
  simp_rw [cavityGaussianCurve_linear, cavityGaussianCurveDerivative_linear]
  exact ((Real.hasDerivAt_cos t).mul_const _).add ((Real.hasDerivAt_sin t).mul_const _)

lemma cavityPenaltyCurve_hasDerivAt {X : Type*} (H V : X → ℝ) (c t : ℝ) (x : X) :
    HasDerivAt (fun s => cavityPenaltyCurve H V c s x)
      (4 * c * Real.sin t * Real.cos t * V x) t := by
  have h := (hasDerivAt_const t (H x)).sub
    ((((Real.hasDerivAt_cos t).pow 2).const_mul (2 * c)).mul_const (V x))
  change HasDerivAt (fun s => H x - 2 * c * Real.cos s ^ 2 * V x) _ t
  convert h using 1
  ring

lemma cavityGaussianCurveDerivative_bound {X : Type*} {d : ℕ}
    (C A : X → Fin d → ℝ) (t : ℝ) (g : Fin d → ℝ) (x : X) :
    |linearGaussian (cavityGaussianCurveDerivative C A t) g x| ≤
      |linearGaussian C g x| + |linearGaussian A g x| := by
  rw [cavityGaussianCurveDerivative_linear]
  calc
    _ ≤ |-Real.sin t * linearGaussian C g x| + |Real.cos t * linearGaussian A g x| := abs_add_le _ _
    _ ≤ _ := by
      simp only [abs_mul, abs_neg]
      exact add_le_add
        ((mul_le_mul_of_nonneg_right (Real.abs_sin_le_one t) (abs_nonneg _)).trans_eq (one_mul _))
        ((mul_le_mul_of_nonneg_right (Real.abs_cos_le_one t) (abs_nonneg _)).trans_eq (one_mul _))

lemma cavityGaussianCurve_cross {X : Type*} {d : ℕ}
    (C A : X → Fin d → ℝ) (t : ℝ) (x y : X)
    (hCA : ∀ x y, gaussianCross C A x y = 0) :
    gaussianCross (cavityGaussianCurveDerivative C A t) (cavityGaussianCurve C A t) x y =
      (Real.sin t * Real.cos t) * (gaussianCross A A x y - gaussianCross C C x y) := by
  have hAC : gaussianCross A C x y = 0 := by
    simpa only [gaussianCross, mul_comm] using hCA y x
  have hexpand : gaussianCross (cavityGaussianCurveDerivative C A t) (cavityGaussianCurve C A t) x y =
      -Real.sin t * Real.cos t * gaussianCross C C x y +
      (-Real.sin t * Real.sin t) * gaussianCross C A x y +
      (Real.cos t * Real.cos t) * gaussianCross A C x y +
      Real.cos t * Real.sin t * gaussianCross A A x y := by
    simp only [gaussianCross, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [cavityGaussianCurveDerivative, cavityGaussianCurve]
    ring
  rw [hexpand, hCA x y, hAC]
  ring

lemma cavityGaussianCurve_cross_bound {X : Type*} {d : ℕ}
    (C A : X → Fin d → ℝ) (V : X → ℝ) (c t : ℝ)
    (hCA : ∀ x y, gaussianCross C A x y = 0)
    (hK : ∀ x y, |gaussianCross A A x y - gaussianCross C C x y| ≤ c * (V x + V y))
    (ht : 0 ≤ Real.sin t * Real.cos t) (x y : X) :
    |gaussianCross (cavityGaussianCurveDerivative C A t) (cavityGaussianCurve C A t) x y| ≤
      (c * Real.sin t * Real.cos t) * (V x + V y) := by
  rw [cavityGaussianCurve_cross C A t x y hCA, abs_mul, abs_of_nonneg ht]
  convert mul_le_mul_of_nonneg_left (hK x y) ht using 1
  ring

end InvariantIsing

end

end OAI
