import OAI.Geometry.IsometricImmersion.Curvature.MetricCurvatureJet
import Mathlib.Analysis.Calculus.ContDiff.Bounds

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

section Smoothness
variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] {t : T}
variable {G : T → MetricMatrix} {D : T → MetricFirstJet} {DD : T → MetricSecondJet}

theorem metricMatrix_inverse_contDiffAt
    (hG : ∀ i j, ContDiffAt ℝ ∞ (fun s => G s i j) t) (hdet : (G t).det ≠ 0)
    (i j : Fin 2) : ContDiffAt ℝ ∞ (fun s => (G s)⁻¹ i j) t := by
  have hdetc : ContDiffAt ℝ ∞ (fun s => (G s).det) t := by
    simp only [Matrix.det_fin_two]
    exact ((hG 0 0).mul (hG 1 1)).sub ((hG 0 1).mul (hG 1 0))
  have hi := hdetc.inv hdet
  have ha : ContDiffAt ℝ ∞ (fun s => (G s).adjugate i j) t := by
    fin_cases i <;> fin_cases j
    · simpa [Matrix.adjugate_fin_two] using hG 1 1
    · convert (hG 0 1).neg using 1
      funext s
      simp [Matrix.adjugate_fin_two]
    · convert (hG 1 0).neg using 1
      funext s
      simp [Matrix.adjugate_fin_two]
    · simpa [Matrix.adjugate_fin_two] using hG 0 0
  have hh : ContDiffAt ℝ ∞ (fun s => (G s).det⁻¹ * (G s).adjugate i j) t := hi.mul ha
  simpa [Matrix.inv_def, Ring.inverse_eq_inv, smul_eq_mul] using hh

theorem inverseDerivativeJet_contDiffAt
    (hG : ∀ i j, ContDiffAt ℝ ∞ (fun s => G s i j) t)
    (hD : ∀ d i j, ContDiffAt ℝ ∞ (fun s => D s d i j) t)
    (hdet : (G t).det ≠ 0) (d i j : Fin 2) :
    ContDiffAt ℝ ∞ (fun s => inverseDerivativeJet (G s) (D s) d i j) t := by
  have hi := metricMatrix_inverse_contDiffAt hG hdet
  have ht (a b : Fin 2) :
      ContDiffAt ℝ ∞ (fun s => (G s)⁻¹ i a * D s d a b * (G s)⁻¹ b j) t :=
    ((hi i a).mul (hD d a b)).mul (hi b j)
  simpa only [inverseDerivativeJet, Fin.sum_univ_two] using
    (((ht 0 0).add (ht 0 1)).add ((ht 1 0).add (ht 1 1))).neg

theorem christoffelJet_contDiffAt
    (hG : ∀ i j, ContDiffAt ℝ ∞ (fun s => G s i j) t)
    (hD : ∀ d i j, ContDiffAt ℝ ∞ (fun s => D s d i j) t)
    (hdet : (G t).det ≠ 0) (k i j : Fin 2) :
    ContDiffAt ℝ ∞ (fun s => christoffelJet (G s) (D s) k i j) t := by
  have hi := metricMatrix_inverse_contDiffAt hG hdet
  have ht (l : Fin 2) : ContDiffAt ℝ ∞
      (fun s => (G s)⁻¹ k l * (D s i j l + D s j i l - D s l i j)) t :=
    (hi k l).mul (((hD i j l).add (hD j i l)).sub (hD l i j))
  simpa only [christoffelJet, Fin.sum_univ_two] using
    (contDiffAt_const (c := (1 / 2 : ℝ))).mul ((ht 0).add (ht 1))

theorem christoffelDerivativeJet_contDiffAt
    (hG : ∀ i j, ContDiffAt ℝ ∞ (fun s => G s i j) t)
    (hD : ∀ d i j, ContDiffAt ℝ ∞ (fun s => D s d i j) t)
    (hDD : ∀ d e i j, ContDiffAt ℝ ∞ (fun s => DD s d e i j) t)
    (hdet : (G t).det ≠ 0) (d k i j : Fin 2) :
    ContDiffAt ℝ ∞ (fun s => christoffelDerivativeJet (G s) (D s) (DD s) d k i j) t := by
  have hi := metricMatrix_inverse_contDiffAt hG hdet
  have hdi := inverseDerivativeJet_contDiffAt hG hD hdet
  have ht (l : Fin 2) : ContDiffAt ℝ ∞ (fun s =>
      inverseDerivativeJet (G s) (D s) d k l * (D s i j l + D s j i l - D s l i j) +
        (G s)⁻¹ k l * (DD s d i j l + DD s d j i l - DD s d l i j)) t :=
    ((hdi d k l).mul (((hD i j l).add (hD j i l)).sub (hD l i j))).add
      ((hi k l).mul (((hDD d i j l).add (hDD d j i l)).sub (hDD d l i j)))
  simpa only [christoffelDerivativeJet, Fin.sum_univ_two] using
    (contDiffAt_const (c := (1 / 2 : ℝ))).mul ((ht 0).add (ht 1))

theorem riemannJet_contDiffAt
    (hG : ∀ i j, ContDiffAt ℝ ∞ (fun s => G s i j) t)
    (hD : ∀ d i j, ContDiffAt ℝ ∞ (fun s => D s d i j) t)
    (hDD : ∀ d e i j, ContDiffAt ℝ ∞ (fun s => DD s d e i j) t)
    (hdet : (G t).det ≠ 0) (l k i j : Fin 2) :
    ContDiffAt ℝ ∞ (fun s => riemannJet (G s) (D s) (DD s) l k i j) t := by
  have hΓ := christoffelJet_contDiffAt hG hD hdet
  have hDΓ := christoffelDerivativeJet_contDiffAt hG hD hDD hdet
  have ht (m : Fin 2) : ContDiffAt ℝ ∞ (fun s =>
      christoffelJet (G s) (D s) m j k * christoffelJet (G s) (D s) l i m -
        christoffelJet (G s) (D s) m i k * christoffelJet (G s) (D s) l j m) t :=
    ((hΓ m j k).mul (hΓ l i m)).sub ((hΓ m i k).mul (hΓ l j m))
  simpa only [riemannJet, Fin.sum_univ_two] using
    ((hDΓ i l j k).sub (hDΓ j l i k)).add ((ht 0).add (ht 1))

theorem curvatureJet_contDiffAt
    (hG : ∀ i j, ContDiffAt ℝ ∞ (fun s => G s i j) t)
    (hD : ∀ d i j, ContDiffAt ℝ ∞ (fun s => D s d i j) t)
    (hDD : ∀ d e i j, ContDiffAt ℝ ∞ (fun s => DD s d e i j) t)
    (hdet : (G t).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun s => curvatureJet (G s) (D s) (DD s)) t := by
  have hR := riemannJet_contDiffAt hG hD hDD hdet
  have hn : ContDiffAt ℝ ∞ (fun s => ∑ l, G s 0 l * riemannJet (G s) (D s) (DD s) l 1 0 1) t := by
    simpa only [Fin.sum_univ_two] using
      ((hG 0 0).mul (hR 0 1 0 1)).add ((hG 0 1).mul (hR 1 1 0 1))
  have hd : ContDiffAt ℝ ∞ (fun s => (G s).det) t := by
    simp only [Matrix.det_fin_two]
    exact ((hG 0 0).mul (hG 1 1)).sub ((hG 0 1).mul (hG 1 0))
  exact hn.div hd hdet

end Smoothness
end SmoothLocal.Geometry

end

end OAI
