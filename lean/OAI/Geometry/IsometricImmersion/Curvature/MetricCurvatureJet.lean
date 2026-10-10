import OAI.Geometry.IsometricImmersion.Calculus.MetricTwoJet
import Mathlib.Tactic.FunProp

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

abbrev MetricMatrix := Matrix (Fin 2) (Fin 2) ℝ
abbrev MetricFirstJet := Fin 2 → MetricMatrix
abbrev MetricSecondJet := Fin 2 → Fin 2 → MetricMatrix

def inverseDerivativeJet (G : MetricMatrix) (D : MetricFirstJet)
    (d i j : Fin 2) : ℝ :=
  -(∑ a, ∑ b, G⁻¹ i a * D d a b * G⁻¹ b j)

def christoffelJet (G : MetricMatrix) (D : MetricFirstJet) (k i j : Fin 2) : ℝ :=
  (1 / 2 : ℝ) * ∑ l, G⁻¹ k l * (D i j l + D j i l - D l i j)

def christoffelDerivativeJet (G : MetricMatrix) (D : MetricFirstJet)
    (DD : MetricSecondJet) (d k i j : Fin 2) : ℝ :=
  (1 / 2 : ℝ) * ∑ l,
    (inverseDerivativeJet G D d k l * (D i j l + D j i l - D l i j) +
      G⁻¹ k l * (DD d i j l + DD d j i l - DD d l i j))

def riemannJet (G : MetricMatrix) (D : MetricFirstJet)
    (DD : MetricSecondJet) (l k i j : Fin 2) : ℝ :=
  christoffelDerivativeJet G D DD i l j k -
    christoffelDerivativeJet G D DD j l i k +
    ∑ m, (christoffelJet G D m j k * christoffelJet G D l i m -
      christoffelJet G D m i k * christoffelJet G D l j m)

def curvatureJet (G : MetricMatrix) (D : MetricFirstJet) (DD : MetricSecondJet) : ℝ :=
  (∑ l, G 0 l * riemannJet G D DD l 1 0 1) / G.det

theorem inverseMetric_coordPartial_eq_jet {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (d i j : Fin 2) :
    coordPartial d (fun q => inverseMetric g q i j) p =
      inverseDerivativeJet (g p) (fun e a b => coordPartial e (fun q => g q a b) p)
        d i j := by
  let D : MetricMatrix := fun a b => coordPartial d (fun q => g q a b) p
  let I' : MetricMatrix := fun a b => coordPartial d (fun q => inverseMetric g q a b) p
  have hprod : D * (g p)⁻¹ + g p * I' = 0 := by
    ext a b
    change (∑ l, D a l * (g p)⁻¹ l b) + (∑ l, g p a l * I' l b) = 0
    simpa only [← Finset.sum_add_distrib, D, I', inverseMetric] using
      metric_inverse_derivative_identity hg hU hp d a b
  have hinv : (g p)⁻¹ * g p = 1 :=
    Matrix.nonsing_inv_mul (g p)
      ((Matrix.isUnit_iff_isUnit_det _).mp (hg.2 p hp).isUnit)
  have hz : ((g p)⁻¹ * D) * (g p)⁻¹ + I' = 0 := by
    calc
      _ = (g p)⁻¹ * (D * (g p)⁻¹ + g p * I') := by
        rw [mul_add, ← mul_assoc, ← mul_assoc, hinv, one_mul]
      _ = 0 := by rw [hprod, mul_zero]
  have hentry : (((g p)⁻¹ * D) * (g p)⁻¹) i j =
      ∑ a, ∑ b, (g p)⁻¹ i a * D a b * (g p)⁻¹ b j := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have heq := congrFun (congrFun hz i) j
  simp only [Matrix.add_apply, Matrix.zero_apply, hentry] at heq
  change I' i j = -(∑ a, ∑ b, (g p)⁻¹ i a * D a b * (g p)⁻¹ b j)
  linarith only [heq]

theorem gaussianCurvature_eq_curvatureJet {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :
    gaussianCurvature g p = curvatureJet (g p)
      (fun d i j => coordPartial d (fun q => g q i j) p)
      (fun d e i j => coordPartial d (coordPartial e (fun q => g q i j)) p) := by
  have hΓ (k i j : Fin 2) : christoffel g k i j p =
      christoffelJet (g p) (fun d i j => coordPartial d (fun q => g q i j) p) k i j := rfl
  have hDΓ (d k i j : Fin 2) : coordPartial d (christoffel g k i j) p =
      christoffelDerivativeJet (g p)
        (fun d i j => coordPartial d (fun q => g q i j) p)
        (fun d e i j => coordPartial d (coordPartial e (fun q => g q i j)) p) d k i j := by
    rw [christoffel_coordPartial_formula hg hU hp]
    have hi := inverseMetric_coordPartial_eq_jet hg hU hp
    simp only [inverseMetric] at hi
    simp only [christoffelDerivativeJet, inverseMetric, hi]
  simp only [gaussianCurvature, curvatureJet, riemann, riemannJet, hΓ, hDΓ]

section Continuity
variable {T : Type*} [TopologicalSpace T] {t : T}
variable {G : T → MetricMatrix} {D : T → MetricFirstJet} {DD : T → MetricSecondJet}

theorem metricMatrix_inverse_continuousAt
    (hG : ∀ i j, ContinuousAt (fun s => G s i j) t) (hdet : (G t).det ≠ 0)
    (i j : Fin 2) : ContinuousAt (fun s => (G s)⁻¹ i j) t := by
  have hdetc : ContinuousAt (fun s => (G s).det) t := by
    simp only [Matrix.det_fin_two]
    exact ((hG 0 0).mul (hG 1 1)).sub ((hG 0 1).mul (hG 1 0))
  have hi := hdetc.inv₀ hdet
  have ha : ContinuousAt (fun s => (G s).adjugate i j) t := by
    fin_cases i <;> fin_cases j
    · simpa [Matrix.adjugate_fin_two] using hG 1 1
    · convert (hG 0 1).neg using 1
      funext s
      simp [Matrix.adjugate_fin_two]
    · convert (hG 1 0).neg using 1
      funext s
      simp [Matrix.adjugate_fin_two]
    · simpa [Matrix.adjugate_fin_two] using hG 0 0
  have hh : ContinuousAt (fun s => (G s).det⁻¹ * (G s).adjugate i j) t := hi.mul ha
  simpa [Matrix.inv_def, Ring.inverse_eq_inv, smul_eq_mul] using hh

theorem inverseDerivativeJet_continuousAt
    (hG : ∀ i j, ContinuousAt (fun s => G s i j) t)
    (hD : ∀ d i j, ContinuousAt (fun s => D s d i j) t)
    (hdet : (G t).det ≠ 0) (d i j : Fin 2) :
    ContinuousAt (fun s => inverseDerivativeJet (G s) (D s) d i j) t := by
  have hi := metricMatrix_inverse_continuousAt hG hdet
  simp only [inverseDerivativeJet, Fin.sum_univ_two]
  fun_prop

theorem christoffelJet_continuousAt
    (hG : ∀ i j, ContinuousAt (fun s => G s i j) t)
    (hD : ∀ d i j, ContinuousAt (fun s => D s d i j) t)
    (hdet : (G t).det ≠ 0) (k i j : Fin 2) :
    ContinuousAt (fun s => christoffelJet (G s) (D s) k i j) t := by
  have hi := metricMatrix_inverse_continuousAt hG hdet
  simp only [christoffelJet, Fin.sum_univ_two]
  fun_prop

theorem christoffelDerivativeJet_continuousAt
    (hG : ∀ i j, ContinuousAt (fun s => G s i j) t)
    (hD : ∀ d i j, ContinuousAt (fun s => D s d i j) t)
    (hDD : ∀ d e i j, ContinuousAt (fun s => DD s d e i j) t)
    (hdet : (G t).det ≠ 0) (d k i j : Fin 2) :
    ContinuousAt (fun s => christoffelDerivativeJet (G s) (D s) (DD s) d k i j) t := by
  have hi := metricMatrix_inverse_continuousAt hG hdet
  have hdi := inverseDerivativeJet_continuousAt hG hD hdet
  simp only [christoffelDerivativeJet, Fin.sum_univ_two]
  fun_prop

theorem riemannJet_continuousAt
    (hG : ∀ i j, ContinuousAt (fun s => G s i j) t)
    (hD : ∀ d i j, ContinuousAt (fun s => D s d i j) t)
    (hDD : ∀ d e i j, ContinuousAt (fun s => DD s d e i j) t)
    (hdet : (G t).det ≠ 0) (l k i j : Fin 2) :
    ContinuousAt (fun s => riemannJet (G s) (D s) (DD s) l k i j) t := by
  have hΓ := christoffelJet_continuousAt hG hD hdet
  have hDΓ := christoffelDerivativeJet_continuousAt hG hD hDD hdet
  simp only [riemannJet, Fin.sum_univ_two]
  fun_prop

theorem curvatureJet_continuousAt
    (hG : ∀ i j, ContinuousAt (fun s => G s i j) t)
    (hD : ∀ d i j, ContinuousAt (fun s => D s d i j) t)
    (hDD : ∀ d e i j, ContinuousAt (fun s => DD s d e i j) t)
    (hdet : (G t).det ≠ 0) :
    ContinuousAt (fun s => curvatureJet (G s) (D s) (DD s)) t := by
  have hR := riemannJet_continuousAt hG hD hDD hdet
  have hn : ContinuousAt (fun s => ∑ l, G s 0 l * riemannJet (G s) (D s) (DD s) l 1 0 1) t := by
    simp only [Fin.sum_univ_two]
    fun_prop
  have hd : ContinuousAt (fun s => (G s).det) t := by
    simp only [Matrix.det_fin_two]
    exact ((hG 0 0).mul (hG 1 1)).sub ((hG 0 1).mul (hG 1 0))
  exact hn.div hd hdet

end Continuity
end SmoothLocal.Geometry

end

end OAI
