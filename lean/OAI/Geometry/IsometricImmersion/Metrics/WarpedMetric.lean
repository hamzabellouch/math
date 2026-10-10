import OAI.Geometry.IsometricImmersion.Metric
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

def warpedMetric (f : Coord → ℝ) : MetricField :=
  fun p => Matrix.diagonal ![1, (f p) ^ 2]

@[simp] theorem warpedMetric_00 (f : Coord → ℝ) (p : Coord) :
    warpedMetric f p 0 0 = 1 := by simp [warpedMetric]

@[simp] theorem warpedMetric_01 (f : Coord → ℝ) (p : Coord) :
    warpedMetric f p 0 1 = 0 := by simp [warpedMetric]

@[simp] theorem warpedMetric_10 (f : Coord → ℝ) (p : Coord) :
    warpedMetric f p 1 0 = 0 := by simp [warpedMetric]

@[simp] theorem warpedMetric_11 (f : Coord → ℝ) (p : Coord) :
    warpedMetric f p 1 1 = (f p) ^ 2 := by simp [warpedMetric]

@[simp] theorem warpedMetric_det (f : Coord → ℝ) (p : Coord) :
    (warpedMetric f p).det = (f p) ^ 2 := by
  simp [Matrix.det_fin_two]

theorem warpedMetric_smoothPositiveOn {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hne : ∀ p ∈ U, f p ≠ 0) :
    SmoothPositiveOn (warpedMetric f) U := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j
    · simpa using (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : Coord => (1 : ℝ)) U)
    · simpa using (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : Coord => (0 : ℝ)) U)
    · simpa using (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : Coord => (0 : ℝ)) U)
    · simpa using hf.pow 2
  · intro p hp
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i
    · simp
    · simpa using sq_pos_of_ne_zero (hne p hp)

theorem inverseMetric_warpedMetric (f : Coord → ℝ) {p : Coord} (hne : f p ≠ 0) :
    inverseMetric (warpedMetric f) p = Matrix.diagonal ![1, ((f p) ^ 2)⁻¹] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [warpedMetric, Matrix.mul_apply, Fin.sum_univ_two, hne]

@[simp] theorem coordPartial_const (i : Fin 2) (c : ℝ) (p : Coord) :
    coordPartial i (fun _ : Coord => c) p = 0 := by
  simp [coordPartial]

theorem coordPartial_mul {f h : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p) (i : Fin 2) :
    coordPartial i (fun q => f q * h q) p =
      coordPartial i f p * h p + f p * coordPartial i h p := by
  simp [coordPartial, fderiv_fun_mul hf hh, add_comm, mul_comm]

theorem coordPartial_neg (f : Coord → ℝ) (i : Fin 2) (p : Coord) :
    coordPartial i (fun q => -f q) p = -coordPartial i f p := by
  simp [coordPartial, fderiv_fun_neg]

theorem coordPartial_sq {f : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (i : Fin 2) :
    coordPartial i (fun q => (f q) ^ 2) p = 2 * f p * coordPartial i f p := by
  simp only [pow_two]
  rw [coordPartial_mul hf hf]
  ring

theorem coordPartial_warpedMetric {f : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (i j k : Fin 2) :
    coordPartial i (fun q => warpedMetric f q j k) p =
      if j = 1 ∧ k = 1 then 2 * f p * coordPartial i f p else 0 := by
  fin_cases j <;> fin_cases k <;> simp [coordPartial_sq hf]

def warpedChristoffel (f : Coord → ℝ) (k i j : Fin 2) (p : Coord) : ℝ :=
  if k = 0 then
    if i = 1 ∧ j = 1 then -(f p * coordPartial 0 f p) else 0
  else if i = 0 ∧ j = 0 then 0
  else if i = 1 ∧ j = 1 then coordPartial 1 f p / f p
  else coordPartial 0 f p / f p

theorem christoffel_warpedMetric {f : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (hne : f p ≠ 0) (k i j : Fin 2) :
    christoffel (warpedMetric f) k i j p = warpedChristoffel f k i j p := by
  simp only [christoffel, Fin.sum_univ_two, inverseMetric_warpedMetric f hne,
    coordPartial_warpedMetric hf]
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [warpedChristoffel] <;> field_simp [hne]

theorem christoffel_warpedMetric_111 {f : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (hne : f p ≠ 0) :
    christoffel (warpedMetric f) 1 1 1 p = coordPartial 1 f p / f p := by
  simpa [warpedChristoffel] using christoffel_warpedMetric hf hne 1 1 1

theorem riemann_warpedMetric_0101 {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    (hne : ∀ q ∈ U, f q ≠ 0) {p : Coord} (hp : p ∈ U) :
    riemann (warpedMetric f) 0 1 0 1 p =
      -(f p * coordPartial 0 (coordPartial 0 f) p) := by
  have hd (q : Coord) (hq : q ∈ U) : DifferentiableAt ℝ f q :=
    ((hf q hq).contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)
  have hdX : DifferentiableAt ℝ (coordPartial 0 f) p :=
    (((partial_contDiffOn hf hU 0) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have h011 : christoffel (warpedMetric f) 0 1 1 =ᶠ[𝓝 p]
      (fun q => -(f q * coordPartial 0 f q)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    simpa [warpedChristoffel] using christoffel_warpedMetric (hd q hq) (hne q hq) 0 1 1
  have h001 : christoffel (warpedMetric f) 0 0 1 =ᶠ[𝓝 p]
      (fun _ : Coord => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    simpa [warpedChristoffel] using christoffel_warpedMetric (hd q hq) (hne q hq) 0 0 1
  have d011 : coordPartial 0 (christoffel (warpedMetric f) 0 1 1) p =
      -(coordPartial 0 f p * coordPartial 0 f p +
        f p * coordPartial 0 (coordPartial 0 f) p) := by
    change fderiv ℝ (christoffel (warpedMetric f) 0 1 1) p (Pi.single 0 1) = _
    rw [h011.fderiv_eq]
    change coordPartial 0 (fun q => -(f q * coordPartial 0 f q)) p = _
    rw [coordPartial_neg, coordPartial_mul (hd p hp) hdX]
  have d001 : coordPartial 1 (christoffel (warpedMetric f) 0 0 1) p = 0 := by
    change fderiv ℝ (christoffel (warpedMetric f) 0 0 1) p (Pi.single 1 1) = _
    rw [h001.fderiv_eq]
    simp
  simp only [riemann, d011, d001, Fin.sum_univ_two,
    christoffel_warpedMetric (hd p hp) (hne p hp)]
  simp [warpedChristoffel]
  field_simp [hne p hp]
  ring

theorem gaussianCurvature_warpedMetric {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    (hne : ∀ q ∈ U, f q ≠ 0) {p : Coord} (hp : p ∈ U) :
    gaussianCurvature (warpedMetric f) p =
      -coordPartial 0 (coordPartial 0 f) p / f p := by
  simp only [gaussianCurvature, Fin.sum_univ_two, warpedMetric_00,
    warpedMetric_01, warpedMetric_det, one_mul, zero_mul, add_zero]
  rw [riemann_warpedMetric_0101 hf hU hne hp]
  field_simp [hne p hp]

end SmoothLocal.Geometry

end

end OAI
