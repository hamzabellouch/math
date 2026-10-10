import OAI.Probability.InvariantIsing.Fields.FieldRealVariance

namespace OAI

/-! The scalar field family carrying exactly the derivatives needed for
finite covariance-coordinate differentiation. No bound on the value is
required: bounded spatial derivative supplies its Gaussian moments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

structure FieldSmoothFamily (I : Set ℝ) where
  U : ℝ × ℝ → ℝ
  X : ℝ × ℝ → ℝ
  XX : ℝ × ℝ → ℝ
  T : ℝ × ℝ → ℝ
  KX : ℝ
  KXX : ℝ
  KT : ℝ
  mU : Measurable U
  mX : Measurable X
  mXX : Measurable XX
  mT : Measurable T
  bX : ∀ p, |X p| ≤ KX
  bXX : ∀ p, |XX p| ≤ KXX
  bT : ∀ p, p.1 ∈ I → |T p| ≤ KT
  derivative : ∀ p, p.1 ∈ I → HasFDerivAt U (pairLinear (T p) (X p)) p
  spatial : ∀ t y, HasDerivAt (fun z => U (t, z)) (X (t, y)) y
  second : ∀ t y, HasDerivAt (fun z => X (t, z)) (XX (t, y)) y

namespace FieldSmoothFamily

variable {I : Set ℝ} (F : FieldSmoothFamily I)

lemma kx_nonneg : 0 ≤ F.KX := (abs_nonneg _).trans (F.bX (0, 0))

lemma growth (t : ℝ) : HasLinearGrowth (fun y => F.U (t, y)) :=
  field_spatial_linearGrowth F.kx_nonneg (fun y => F.bX (t, y)) (F.spatial t)

def value (a v ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  gaussianTransform (a + v * p.1) ζ (fun y => F.U (p.1, y)) p.2

def mean (a v ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  gaussianTiltAverage (a + v * p.1) ζ (fun y => F.U (p.1, y))
    (fun y => F.X (p.1, y)) p.2

def curvature (a v ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  gaussianTiltAverage (a + v * p.1) ζ (fun y => F.U (p.1, y))
    (fun y => F.XX (p.1, y)) p.2 + ζ *
      (gaussianTiltAverage (a + v * p.1) ζ (fun y => F.U (p.1, y))
        (fun y => (F.X (p.1, y)) ^ 2) p.2 - (F.mean a v ζ p) ^ 2)

def tangent (a v ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  gaussianTiltAverage (a + v * p.1) ζ (fun y => F.U (p.1, y))
    (fun y => F.T (p.1, y)) p.2 + v / 2 *
      gaussianTiltAverage (a + v * p.1) ζ (fun y => F.U (p.1, y))
        (fun y => F.XX (p.1, y) + ζ * (F.X (p.1, y)) ^ 2) p.2

lemma measurable_value (a v ζ : ℝ) : Measurable (F.value a v ζ) :=
  measurable_gaussianTransform_param (F.mU.comp (by fun_prop)) (by fun_prop) (by fun_prop) ζ

lemma measurable_mean (a v ζ : ℝ) : Measurable (F.mean a v ζ) :=
  measurable_gaussianTiltAverage_param (F.mU.comp (by fun_prop))
    (F.mX.comp (by fun_prop)) (by fun_prop) (by fun_prop) ζ

lemma measurable_curvature (a v ζ : ℝ) : Measurable (F.curvature a v ζ) := by
  exact (measurable_gaussianTiltAverage_param (F.mU.comp (by fun_prop))
    (F.mXX.comp (by fun_prop)) (by fun_prop) (by fun_prop) ζ).add
      (((measurable_gaussianTiltAverage_param (F.mU.comp (by fun_prop))
        ((F.mX.pow_const 2).comp (by fun_prop)) (by fun_prop) (by fun_prop) ζ).sub
          ((F.measurable_mean a v ζ).pow_const 2)).const_mul ζ)

lemma measurable_tangent (a v ζ : ℝ) : Measurable (F.tangent a v ζ) := by
  exact (measurable_gaussianTiltAverage_param (F.mU.comp (by fun_prop))
    (F.mT.comp (by fun_prop)) (by fun_prop) (by fun_prop) ζ).add
      ((measurable_gaussianTiltAverage_param (F.mU.comp (by fun_prop))
        ((F.mXX.add ((F.mX.pow_const 2).const_mul ζ)).comp (by fun_prop))
          (by fun_prop) (by fun_prop) ζ).const_mul (v / 2))

lemma bound_mean (a v ζ : ℝ) (p : ℝ × ℝ) : |F.mean a v ζ p| ≤ F.KX :=
  field_gaussianTiltAverage_bound _ _ (F.mU.comp (by fun_prop)) (F.growth p.1)
    (F.mX.comp (by fun_prop)) (fun y => F.bX (p.1, y)) p.2

lemma bound_curvature (a v ζ : ℝ) (p : ℝ × ℝ) :
    |F.curvature a v ζ p| ≤ F.KXX + 2 * |ζ| * F.KX ^ 2 := by
  have hXX := field_gaussianTiltAverage_bound (a + v * p.1) ζ
    (F.mU.comp (by fun_prop)) (F.growth p.1) (F.mXX.comp (by fun_prop))
    (fun y => F.bXX (p.1, y)) p.2
  have hsq : ∀ y, |(F.X (p.1, y)) ^ 2| ≤ F.KX ^ 2 := fun y => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (F.bX (p.1, y)) 2
  have hsqavg := field_gaussianTiltAverage_bound (a + v * p.1) ζ
    (F.mU.comp (by fun_prop)) (F.growth p.1) ((F.mX.pow_const 2).comp (by fun_prop)) hsq p.2
  have hmean : |(F.mean a v ζ p) ^ 2| ≤ F.KX ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (F.bound_mean a v ζ p) 2
  unfold curvature
  refine (abs_add_le _ _).trans (add_le_add hXX ?_)
  rw [abs_mul]
  calc
    _ ≤ |ζ| * (|gaussianTiltAverage (a + v * p.1) ζ (fun y => F.U (p.1, y))
          (fun y => (F.X (p.1, y)) ^ 2) p.2| + |(F.mean a v ζ p) ^ 2|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg ζ)
    _ ≤ |ζ| * (F.KX ^ 2 + F.KX ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hsqavg hmean) (abs_nonneg ζ)
    _ = _ := by ring

lemma bound_tangent (a v ζ : ℝ) {p : ℝ × ℝ} (hp : p.1 ∈ I) :
    |F.tangent a v ζ p| ≤ F.KT + |v| / 2 * (F.KXX + |ζ| * F.KX ^ 2) := by
  have hT := field_gaussianTiltAverage_bound (a + v * p.1) ζ
    (F.mU.comp (by fun_prop)) (F.growth p.1) (F.mT.comp (by fun_prop))
    (fun y => F.bT (p.1, y) hp) p.2
  have hgen : ∀ y, |F.XX (p.1, y) + ζ * (F.X (p.1, y)) ^ 2| ≤
      F.KXX + |ζ| * F.KX ^ 2 :=
    bounded_generator (fun y => F.bX (p.1, y)) (fun y => F.bXX (p.1, y)) ζ
  have hQ := field_gaussianTiltAverage_bound (a + v * p.1) ζ
    (F.mU.comp (by fun_prop)) (F.growth p.1)
    ((F.mXX.add ((F.mX.pow_const 2).const_mul ζ)).comp (by fun_prop)) hgen p.2
  unfold tangent
  refine (abs_add_le _ _).trans (add_le_add hT ?_)
  rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul_of_nonneg_left hQ (by positivity)

lemma spatial_value (a v ζ t y : ℝ) :
    HasDerivAt (fun z => F.value a v ζ (t, z)) (F.mean a v ζ (t, y)) y := by
  exact field_gaussianTransform_hasDerivAt (a + v * t) ζ
    (F.mU.comp (by fun_prop)) (F.growth t) (F.mX.comp (by fun_prop))
    F.kx_nonneg (fun z => F.bX (t, z)) (F.spatial t) y

lemma spatial_mean (a v ζ t y : ℝ) :
    HasDerivAt (fun z => F.mean a v ζ (t, z)) (F.curvature a v ζ (t, y)) y := by
  have h := field_gaussianTiltAverage_hasDerivAt (a + v * t) ζ
    (F := fun u => F.U (t, u)) (D := fun u => F.X (t, u))
    (a := fun u => F.X (t, u)) (b := fun u => F.XX (t, u))
    (F.mU.comp (by fun_prop)) (F.growth t) (F.mX.comp (by fun_prop))
    (F.mX.comp (by fun_prop)) (F.mXX.comp (by fun_prop)) F.kx_nonneg F.kx_nonneg
    (fun z => F.bX (t, z)) (fun z => F.bX (t, z)) (fun z => F.bXX (t, z))
    (F.spatial t) (F.second t) y
  simpa only [mean, curvature, pow_two, Function.comp_apply] using h

def transform (hI : IsOpen I) (a v ζ : ℝ) (hv : ∀ t ∈ I, 0 < a + v * t) :
    FieldSmoothFamily I where
  U := F.value a v ζ
  X := F.mean a v ζ
  XX := F.curvature a v ζ
  T := F.tangent a v ζ
  KX := F.KX
  KXX := F.KXX + 2 * |ζ| * F.KX ^ 2
  KT := F.KT + |v| / 2 * (F.KXX + |ζ| * F.KX ^ 2)
  mU := F.measurable_value a v ζ
  mX := F.measurable_mean a v ζ
  mXX := F.measurable_curvature a v ζ
  mT := F.measurable_tangent a v ζ
  bX := F.bound_mean a v ζ
  bXX := F.bound_curvature a v ζ
  bT := fun _ hp => F.bound_tangent a v ζ hp
  derivative := fun p hp => field_gaussianFamily_local_hasFDerivAt hI F.mU F.mT F.mX F.mXX
    F.bT F.bX F.bXX F.derivative F.spatial F.second a v ζ hp (hv p.1 hp)
  spatial := F.spatial_value a v ζ
  second := F.spatial_mean a v ζ

end FieldSmoothFamily
end InvariantIsing

end

end OAI
