import OAI.Geometry.IsometricImmersion.Curvature.MetricCurvatureJet
import OAI.Geometry.IsometricImmersion.Metrics.MetricLocality
import Mathlib.Tactic.LinearCombination

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def lowerChristoffelDerivativeJet (G : MetricMatrix) (D : MetricFirstJet)
    (d k i j : Fin 2) : ℝ :=
  (1/2 : ℝ) * ∑ l, inverseDerivativeJet G D d k l * (D i j l+D j i l-D l i j)

def curvatureLowerJet (G : MetricMatrix) (D : MetricFirstJet) : ℝ :=
  ∑ l, G 0 l * (lowerChristoffelDerivativeJet G D 0 l 1 1 -
    lowerChristoffelDerivativeJet G D 1 l 0 1 +
    ∑ m, (christoffelJet G D m 1 1 * christoffelJet G D l 0 m -
      christoffelJet G D m 0 1 * christoffelJet G D l 1 m))

def metricFirstJet (g : MetricField) (p : Coord) : MetricFirstJet :=
  fun d i j => coordPartial d (fun q => g q i j) p

def curvatureLowerTerm (g : MetricField) (p : Coord) : ℝ :=
  curvatureLowerJet (g p) (metricFirstJet g p)

theorem metric_inverse_first_row_contraction (G : MetricMatrix) (hdet : G.det ≠ 0)
    (T : Fin 2 → ℝ) :
    (∑ l, G 0 l * ∑ a, G⁻¹ l a * T a) = T 0 := by
  have hi := Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hdet)
  have h0 := congrFun (congrFun hi 0) 0
  have h1 := congrFun (congrFun hi 0) 1
  simp only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply,ite_true,
    show (0 : Fin 2) ≠ 1 by decide,ite_false] at h0 h1
  calc
    _ = (G 0 0*G⁻¹ 0 0+G 0 1*G⁻¹ 1 0)*T 0 +
        (G 0 0*G⁻¹ 0 1+G 0 1*G⁻¹ 1 1)*T 1 := by
      simp only [Fin.sum_univ_two]
      ring
    _ = T 0 := by rw [h0,h1]; ring

theorem curvatureJet_density_raw (G : MetricMatrix) (D : MetricFirstJet)
    (DD : MetricSecondJet) (hdet : G.det ≠ 0) :
    curvatureJet G D DD * G.det =
      (1/2 : ℝ)*(DD 0 1 1 0+DD 0 1 1 0-DD 0 0 1 1-
        DD 1 0 1 0-DD 1 1 0 0+DD 1 0 0 1) + curvatureLowerJet G D := by
  let T : Fin 2 → ℝ := fun a => DD 0 1 1 a+DD 0 1 1 a-DD 0 a 1 1-
    DD 1 0 1 a-DD 1 1 0 a+DD 1 a 0 1
  have hc := metric_inverse_first_row_contraction G hdet T
  simp only [T,Fin.sum_univ_two] at hc
  rw [curvatureJet,div_mul_cancel₀ _ hdet]
  simp only [riemannJet,christoffelDerivativeJet,curvatureLowerJet,
    lowerChristoffelDerivativeJet,Fin.sum_univ_two]
  linear_combination (1/2 : ℝ)*hc

theorem metric_coeff_second_partial_symm {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (d e i j : Fin 2) :
    coordPartial d (coordPartial e (fun q => g q i j)) p =
      coordPartial d (coordPartial e (fun q => g q j i)) p := by
  have he : coordPartial e (fun q => g q i j) =ᶠ[𝓝 p]
      coordPartial e (fun q => g q j i) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact metric_coeff_partial_symm hg hU hq e i j
  exact coordPartial_eq_of_eventuallyEq he d

theorem gaussianCurvature_density_principal_part {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :
    gaussianCurvature g p * (g p).det =
      coordPartial 0 (coordPartial 1 (fun q => g q 0 1)) p -
        (coordPartial 0 (coordPartial 0 (fun q => g q 1 1)) p +
          coordPartial 1 (coordPartial 1 (fun q => g q 0 0)) p)/2 +
        curvatureLowerTerm g p := by
  have hraw := curvatureJet_density_raw (g p) (metricFirstJet g p)
    (fun (d e i j : Fin 2) => coordPartial d (coordPartial e (fun q => g q i j)) p)
    (metricDet_ne_zero hg hp)
  have hfull := (congrArg (fun k : ℝ => k * (g p).det)
    (gaussianCurvature_eq_curvatureJet hg hU hp)).trans hraw
  rw [metric_coeff_second_partial_symm hg hU hp 0 1 1 0,
    metric_coeff_second_partial_symm hg hU hp 1 0 1 0,
    coordPartial_comm (hg.1 0 1) hU hp 1 0] at hfull
  rw [hfull]
  dsimp only [curvatureLowerTerm,metricFirstJet]
  ring

section SmoothLowerJet
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {S : Set E} {G : E → MetricMatrix} {D : E → MetricFirstJet}

theorem metricMatrix_inverse_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun s => G s i j) S)
    (hdet : ∀ s ∈ S, (G s).det ≠ 0) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun s => (G s)⁻¹ i j) S := by
  have hd : ContDiffOn ℝ ∞ (fun s => (G s).det) S := by
    simp only [Matrix.det_fin_two]
    exact ((hG 0 0).mul (hG 1 1)).sub ((hG 0 1).mul (hG 1 0))
  have ha : ContDiffOn ℝ ∞ (fun s => (G s).adjugate i j) S := by
    fin_cases i <;> fin_cases j
    · simpa [Matrix.adjugate_fin_two] using hG 1 1
    · simpa [Matrix.adjugate_fin_two] using (hG 0 1).neg
    · simpa [Matrix.adjugate_fin_two] using (hG 1 0).neg
    · simpa [Matrix.adjugate_fin_two] using hG 0 0
  simpa [Matrix.inv_def,Ring.inverse_eq_inv,smul_eq_mul] using (hd.inv hdet).mul ha

theorem inverseDerivativeJet_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun s => G s i j) S)
    (hD : ∀ d i j, ContDiffOn ℝ ∞ (fun s => D s d i j) S)
    (hdet : ∀ s ∈ S, (G s).det ≠ 0) (d i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun s => inverseDerivativeJet (G s) (D s) d i j) S := by
  have hi := metricMatrix_inverse_contDiffOn hG hdet
  have ht (a b : Fin 2) :
      ContDiffOn ℝ ∞ (fun s => (G s)⁻¹ i a * D s d a b * (G s)⁻¹ b j) S :=
    ((hi i a).mul (hD d a b)).mul (hi b j)
  simpa only [inverseDerivativeJet,Fin.sum_univ_two] using
    (((ht 0 0).add (ht 0 1)).add ((ht 1 0).add (ht 1 1))).neg

theorem christoffelJet_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun s => G s i j) S)
    (hD : ∀ d i j, ContDiffOn ℝ ∞ (fun s => D s d i j) S)
    (hdet : ∀ s ∈ S, (G s).det ≠ 0) (k i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun s => christoffelJet (G s) (D s) k i j) S := by
  have hi := metricMatrix_inverse_contDiffOn hG hdet
  have ht (l : Fin 2) : ContDiffOn ℝ ∞
      (fun s => (G s)⁻¹ k l * (D s i j l+D s j i l-D s l i j)) S :=
    (hi k l).mul (((hD i j l).add (hD j i l)).sub (hD l i j))
  simpa only [christoffelJet,Fin.sum_univ_two] using
    (contDiffOn_const (c := (1/2 : ℝ))).mul ((ht 0).add (ht 1))

theorem lowerChristoffelDerivativeJet_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun s => G s i j) S)
    (hD : ∀ d i j, ContDiffOn ℝ ∞ (fun s => D s d i j) S)
    (hdet : ∀ s ∈ S, (G s).det ≠ 0) (d k i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun s => lowerChristoffelDerivativeJet (G s) (D s) d k i j) S := by
  have hi := inverseDerivativeJet_contDiffOn hG hD hdet
  have ht (l : Fin 2) : ContDiffOn ℝ ∞
      (fun s => inverseDerivativeJet (G s) (D s) d k l *
        (D s i j l+D s j i l-D s l i j)) S :=
    (hi d k l).mul (((hD i j l).add (hD j i l)).sub (hD l i j))
  simpa only [lowerChristoffelDerivativeJet,Fin.sum_univ_two] using
    (contDiffOn_const (c := (1/2 : ℝ))).mul ((ht 0).add (ht 1))

theorem curvatureLowerJet_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun s => G s i j) S)
    (hD : ∀ d i j, ContDiffOn ℝ ∞ (fun s => D s d i j) S)
    (hdet : ∀ s ∈ S, (G s).det ≠ 0) :
    ContDiffOn ℝ ∞ (fun s => curvatureLowerJet (G s) (D s)) S := by
  have hΓ := christoffelJet_contDiffOn hG hD hdet
  have hΓD := lowerChristoffelDerivativeJet_contDiffOn hG hD hdet
  have ht (l m : Fin 2) : ContDiffOn ℝ ∞ (fun s =>
      christoffelJet (G s) (D s) m 1 1 * christoffelJet (G s) (D s) l 0 m -
        christoffelJet (G s) (D s) m 0 1 * christoffelJet (G s) (D s) l 1 m) S :=
    ((hΓ m 1 1).mul (hΓ l 0 m)).sub ((hΓ m 0 1).mul (hΓ l 1 m))
  have hl (l : Fin 2) : ContDiffOn ℝ ∞ (fun s => G s 0 l *
      (lowerChristoffelDerivativeJet (G s) (D s) 0 l 1 1 -
        lowerChristoffelDerivativeJet (G s) (D s) 1 l 0 1 +
        ∑ m, (christoffelJet (G s) (D s) m 1 1 * christoffelJet (G s) (D s) l 0 m -
          christoffelJet (G s) (D s) m 0 1 * christoffelJet (G s) (D s) l 1 m))) S := by
    simpa only [Fin.sum_univ_two] using
      (hG 0 l).mul (((hΓD 0 l 1 1).sub (hΓD 1 l 0 1)).add ((ht l 0).add (ht l 1)))
  simpa only [curvatureLowerJet,Fin.sum_univ_two] using (hl 0).add (hl 1)

end SmoothLowerJet

theorem curvatureLowerTerm_contDiffOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (curvatureLowerTerm g) U :=
  curvatureLowerJet_contDiffOn hg.1
    (fun d i j => partial_contDiffOn (hg.1 i j) hU d) (fun _ hp => metricDet_ne_zero hg hp)

end SmoothLocal.Geometry

end

end OAI
