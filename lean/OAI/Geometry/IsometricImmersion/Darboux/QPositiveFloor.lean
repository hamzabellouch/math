import OAI.Geometry.IsometricImmersion.Coordinates.ActualShearHyperbolicity
import OAI.Geometry.IsometricImmersion.Darboux.QHighEquation
import OAI.Geometry.IsometricImmersion.Calculus.MetricInverseJetBounds
import OAI.Geometry.IsometricImmersion.Immersions.BoundedHeightClasses

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix BigOperators

namespace SmoothLocal.Geometry

def pointHessianBound (G Z d : ℝ) : ℝ := Z + 6 * (G / d) * G * Z

theorem pointHessianBound_nonneg {G Z d : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) : 0 ≤ pointHessianBound G Z d := by
  unfold pointHessianBound
  positivity

theorem inverseMetric_value_bound {g : MetricField} {p : Coord} {G d : ℝ}
    (hG : 0 ≤ G) (hd : 0 < d) (hg0 : ∀ i j, |g p i j| ≤ G)
    (hdet : d ≤ |(g p).det|) (i j : Fin 2) : |inverseMetric g p i j| ≤ G / d := by
  have hadj : |(g p).adjugate i j| ≤ G := by
    fin_cases i <;> fin_cases j
    · simpa [Matrix.adjugate_fin_two] using hg0 1 1
    · simpa [Matrix.adjugate_fin_two] using hg0 0 1
    · simpa [Matrix.adjugate_fin_two] using hg0 1 0
    · simpa [Matrix.adjugate_fin_two] using hg0 0 0
  have he := congrFun (inverseMetric_eq_adjugate_div g i j) p
  rw [he, abs_div]
  exact (div_le_div_of_nonneg_right hadj (abs_nonneg _)).trans
    (div_le_div_of_nonneg_left hG hd hdet)

theorem christoffel_value_bound {g : MetricField} {p : Coord} {G d : ℝ}
    (hG : 0 ≤ G) (hd : 0 < d) (hg0 : ∀ i j, |g p i j| ≤ G)
    (hg1 : ∀ a i j, |coordPartial a (fun q => g q i j) p| ≤ G)
    (hdet : d ≤ |(g p).det|) (k i j : Fin 2) :
    |christoffel g k i j p| ≤ 3 * (G / d) * G := by
  have hB (l : Fin 2) : |coordPartial i (fun q => g q j l) p +
      coordPartial j (fun q => g q i l) p - coordPartial l (fun q => g q i j) p| ≤ 3 * G :=
    (abs_sub _ _).trans ((add_le_add
      ((abs_add_le _ _).trans (add_le_add (hg1 i j l) (hg1 j i l))) le_rfl).trans
      (by linarith [hg1 l i j]))
  have hprod (l : Fin 2) : |inverseMetric g p k l *
      (coordPartial i (fun q => g q j l) p + coordPartial j (fun q => g q i l) p -
        coordPartial l (fun q => g q i j) p)| ≤ (G / d) * (3 * G) := by
    rw [abs_mul]
    exact mul_le_mul (inverseMetric_value_bound hG hd hg0 hdet k l) (hB l)
      (abs_nonneg _) (div_nonneg hG hd.le)
  unfold christoffel
  rw [Fin.sum_univ_two, abs_mul]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    _ ≤ (1 / 2 : ℝ) * (|inverseMetric g p k 0 *
        (coordPartial i (fun q => g q j 0) p + coordPartial j (fun q => g q i 0) p -
          coordPartial 0 (fun q => g q i j) p)| + |inverseMetric g p k 1 *
        (coordPartial i (fun q => g q j 1) p + coordPartial j (fun q => g q i 1) p -
          coordPartial 1 (fun q => g q i j) p)|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * ((G / d) * (3 * G) + (G / d) * (3 * G)) :=
      mul_le_mul_of_nonneg_left (add_le_add (hprod 0) (hprod 1)) (by norm_num)
    _ = _ := by ring

theorem covHessian_value_bound {g : MetricField} {z : Coord → ℝ} {p : Coord} {G Z d : ℝ}
    (hG : 0 ≤ G) (_hZ : 0 ≤ Z) (hd : 0 < d)
    (hg0 : ∀ i j, |g p i j| ≤ G)
    (hg1 : ∀ a i j, |coordPartial a (fun q => g q i j) p| ≤ G)
    (hz1 : ∀ i, |coordPartial i z p| ≤ Z)
    (hz2 : ∀ i j, |coordPartial i (coordPartial j z) p| ≤ Z)
    (hdet : d ≤ |(g p).det|) (i j : Fin 2) :
    |covHessian g z p i j| ≤ pointHessianBound G Z d := by
  have hprod (k : Fin 2) : |christoffel g k i j p * coordPartial k z p| ≤
      (3 * (G / d) * G) * Z := by
    rw [abs_mul]
    exact mul_le_mul (christoffel_value_bound hG hd hg0 hg1 hdet k i j) (hz1 k)
      (abs_nonneg _) (by positivity)
  unfold covHessian
  rw [Fin.sum_univ_two]
  calc
    _ ≤ |coordPartial i (coordPartial j z) p| +
        |christoffel g 0 i j p * coordPartial 0 z p +
          christoffel g 1 i j p * coordPartial 1 z p| := abs_sub _ _
    _ ≤ Z + (|christoffel g 0 i j p * coordPartial 0 z p| +
        |christoffel g 1 i j p * coordPartial 1 z p|) :=
      add_le_add (hz2 i j) (abs_add_le _ _)
    _ ≤ Z + ((3 * (G / d) * G) * Z + (3 * (G / d) * G) * Z) :=
      add_le_add le_rfl (add_le_add (hprod 0) (hprod 1))
    _ = pointHessianBound G Z d := by unfold pointHessianBound; ring

end SmoothLocal.Geometry

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Flow

def shearedHessianUpper (G Z d q0 : ℝ) : ℝ :=
  1 + (1 + |q0|)^2 * pointHessianBound G Z d

def shearedQPositiveFloor (G Z d q0 M : ℝ) : ℝ :=
  1 / (M * shearedHessianUpper G Z d q0)

theorem shearedHessianUpper_pos {G Z d : ℝ} (q0 : ℝ)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) : 0 < shearedHessianUpper G Z d q0 := by
  have hH := pointHessianBound_nonneg hG hZ hd
  unfold shearedHessianUpper
  positivity

theorem shearedQPositiveFloor_pos {G Z d M : ℝ} (q0 : ℝ)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hM : 0 < M) :
    0 < shearedQPositiveFloor G Z d q0 M :=
  one_div_pos.mpr (mul_pos hM (shearedHessianUpper_pos q0 hG hZ hd))

theorem sheared_Hxx_value_bound
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord} {G Z d : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (q0 : ℝ) (hp : inverseShearCoordinates q0 p ∈ U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d)
    (hg0 : ∀ i j, |g (inverseShearCoordinates q0 p) i j| ≤ G)
    (hg1 : ∀ a i j, |coordPartial a (fun q => g q i j) (inverseShearCoordinates q0 p)| ≤ G)
    (hz1 : ∀ i, |coordPartial i z (inverseShearCoordinates q0 p)| ≤ Z)
    (hz2 : ∀ i j, |coordPartial i (coordPartial j z) (inverseShearCoordinates q0 p)| ≤ Z)
    (hdet : d ≤ |(g (inverseShearCoordinates q0 p)).det|) :
    |covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p 0 0| ≤
      shearedHessianUpper G Z d q0 := by
  let H := pointHessianBound G Z d
  have hHN : 0 ≤ H := pointHessianBound_nonneg hG hZ hd
  have hH (i j : Fin 2) := covHessian_value_bound hG hZ hd hg0 hg1 hz1 hz2 hdet i j
  have he := (covHessian_shear_entries hg hz hU q0 hp).2.2
  rw [he]
  have hq : |q0^2| = |q0|^2 := abs_pow q0 2
  calc
    _ ≤ |covHessian g z (inverseShearCoordinates q0 p) 0 0 -
        2 * q0 * covHessian g z (inverseShearCoordinates q0 p) 0 1| +
        |q0^2 * covHessian g z (inverseShearCoordinates q0 p) 1 1| := abs_add_le _ _
    _ ≤ (|covHessian g z (inverseShearCoordinates q0 p) 0 0| +
        |2 * q0 * covHessian g z (inverseShearCoordinates q0 p) 0 1|) +
        |q0^2 * covHessian g z (inverseShearCoordinates q0 p) 1 1| :=
      add_le_add (abs_sub _ _) le_rfl
    _ ≤ H + 2 * |q0| * H + |q0|^2 * H := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), hq]
      exact add_le_add (add_le_add (hH 0 0)
        (mul_le_mul_of_nonneg_left (hH 0 1) (by positivity)))
        (mul_le_mul_of_nonneg_left (hH 1 1) (sq_nonneg _))
    _ ≤ shearedHessianUpper G Z d q0 := by
      change H + 2 * |q0| * H + |q0|^2 * H ≤ 1 + (1 + |q0|)^2 * H
      nlinarith

theorem positive_negative_ratio_floor {a b M H : ℝ}
    (hM : 0 < M) (hH : 0 < H) (hb : b ≠ 0)
    (hpos : 0 < -(a / b)) (ha : 1 / M ≤ |a|) (hupper : |b| ≤ H) :
    1 / (M * H) ≤ -(a / b) := by
  have hratio : -(a / b) = |a| / |b| := by
    rw [← abs_of_pos hpos, abs_neg, abs_div]
  rw [hratio]
  calc
    1 / (M * H) = (1 / M) / H := by rw [div_div]
    _ ≤ |a| / H := div_le_div_of_nonneg_right ha hH.le
    _ ≤ |a| / |b| := div_le_div_of_nonneg_left
      ((one_div_pos.mpr hM).le.trans ha) (abs_pos.mpr hb) hupper

theorem actual_sheared_Q5_floor
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord} {G Z d M : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (q0 : ℝ) (hp : inverseShearCoordinates q0 p ∈ U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hM : 0 < M)
    (hg0 : ∀ i j, |g (inverseShearCoordinates q0 p) i j| ≤ G)
    (hg1 : ∀ a i j, |coordPartial a (fun q => g q i j) (inverseShearCoordinates q0 p)| ≤ G)
    (hz1 : ∀ i, |coordPartial i z (inverseShearCoordinates q0 p)| ≤ Z)
    (hz2 : ∀ i j, |coordPartial i (coordPartial j z) (inverseShearCoordinates q0 p)| ≤ Z)
    (hdet : d ≤ |(g (inverseShearCoordinates q0 p)).det|)
    (hyy : 1 / M ≤ |covHessian g z (inverseShearCoordinates q0 p) 1 1|)
    (hD : (covHessian g z (inverseShearCoordinates q0 p)).det =
      gaussianCurvature g (inverseShearCoordinates q0 p) * heightEnergy g z (inverseShearCoordinates q0 p))
    (hxx : covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p 0 0 ≠ 0)
    (hS : 0 < heightQCoefficient (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) 5 p) :
    shearedQPositiveFloor G Z d q0 M ≤
      heightQCoefficient (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) 5 p := by
  have hUS := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hgS := metricInShearCoordinates_smoothPositive hg q0
  have hzS := heightInShearCoordinates_contDiffOn hz q0
  have hD' := darboux_in_shear_coordinates hg hz hU q0 hp hD
  have hQ := q_xx_coefficient_at_height hgS hUS hzS hp hxx hD'
  change heightQCoefficient (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) 5 p = _ at hQ
  have h11 := (covHessian_shear_entries hg hz hU q0 hp).1
  rw [hQ] at hS ⊢
  apply positive_negative_ratio_floor hM (shearedHessianUpper_pos q0 hG hZ hd) hxx hS
  · simpa only [h11] using hyy
  · exact sheared_Hxx_value_bound hg hU hz q0 hp hG hZ hd hg0 hg1 hz1 hz2 hdet

end SmoothLocal.Pulse

end

end OAI
