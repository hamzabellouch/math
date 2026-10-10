import OAI.Geometry.IsometricImmersion.Metric
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter
namespace SmoothLocal.Geometry

section Calculus
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {F : Coord → V} {U : Set Coord} {p : Coord}

theorem second_coordPartial_eq_fderiv (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hp : p ∈ U) (i j : Fin 2) :
    coordPartial i (coordPartial j F) p =
      fderiv ℝ (fderiv ℝ F) p (Pi.single i 1) (Pi.single j 1) := by
  have hs : ContDiffOn ℝ ∞ (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hs p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  unfold coordPartial
  rw [fderiv_clm_apply hd (differentiableAt_const (c := Pi.single j (1 : ℝ)))]
  simp

theorem coordPartial_comm (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hp : p ∈ U) (i j : Fin 2) :
    coordPartial i (coordPartial j F) p = coordPartial j (coordPartial i F) p := by
  rw [second_coordPartial_eq_fderiv hF hU hp, second_coordPartial_eq_fderiv hF hU hp]
  exact (((hF p hp).contDiffAt (hU.mem_nhds hp)).isSymmSndFDerivAt
    (by
      simp only [minSmoothness, ite_eq_left (inferInstance : IsRCLikeNormedField ℝ)]
      exact WithTop.coe_le_coe.mpr le_top)) _ _

end Calculus

def inducedMetric (F : Coord → Ambient) : MetricField := fun p i j =>
  inner ℝ (coordPartial i F p) (coordPartial j F p)

theorem inducedMetric_eq_of_isometric {g : MetricField} {F : Coord → Ambient}
    {U : Set Coord} (hF : IsometricOn g F U) {p : Coord} (hp : p ∈ U) :
    inducedMetric F p = g p := by
  ext i j
  simpa [inducedMetric, coordPartial, Matrix.mulVec_single_one,
    dotProduct, Pi.single_apply] using hF.2 p hp (Pi.single i 1) (Pi.single j 1)

theorem metric_partial_eq {g : MetricField} {F : Coord → Ambient}
    {U : Set Coord} (hF : IsometricOn g F U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) (i j k : Fin 2) :
    coordPartial k (fun q => g q i j) p =
      inner ℝ (coordPartial k (coordPartial i F) p) (coordPartial j F p) +
      inner ℝ (coordPartial i F p) (coordPartial k (coordPartial j F) p) := by
  have hl : (fun q => g q i j) =ᶠ[𝓝 p] (fun q => inducedMetric F q i j) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact congrFun (congrFun (inducedMetric_eq_of_isometric hF hq).symm i) j
  have hd (l : Fin 2) : DifferentiableAt ℝ (coordPartial l F) p :=
    (((partial_contDiffOn hF.1 hU l) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  unfold coordPartial
  rw [hl.fderiv_eq]
  change fderiv ℝ (fun q => inner ℝ (coordPartial i F q) (coordPartial j F q)) p
    (Pi.single k 1) = _
  rw [fderiv_inner_apply ℝ (hd i) (hd j)]
  change inner ℝ (coordPartial i F p) (coordPartial k (coordPartial j F) p) +
    inner ℝ (coordPartial k (coordPartial i F) p) (coordPartial j F p) = _
  exact add_comm _ _

theorem second_partial_inner_tangent {g : MetricField} {F : Coord → Ambient}
    {U : Set Coord} (hF : IsometricOn g F U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) (i j l : Fin 2) :
    inner ℝ (coordPartial i (coordPartial j F) p) (coordPartial l F p) =
      (coordPartial i (fun q => g q j l) p +
        coordPartial j (fun q => g q i l) p -
        coordPartial l (fun q => g q i j) p) / 2 := by
  rw [metric_partial_eq hF hU hp, metric_partial_eq hF hU hp,
    metric_partial_eq hF hU hp]
  rw [coordPartial_comm hF.1 hU hp j i,
    coordPartial_comm hF.1 hU hp l i, coordPartial_comm hF.1 hU hp l j]
  rw [real_inner_comm (coordPartial j F p) (coordPartial i (coordPartial l F) p)]
  ring

end SmoothLocal.Geometry

end

end OAI
