import OAI.Geometry.EinsteinFour.CoordinateMetricCompatibility
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

namespace OAI

/-! Smoothness of the actual pulled-back metric in a chart. The tangent
vectors are transported by the derivative of the inverse chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle
open scoped Manifold ContDiff Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem chart_inverse_vector_smooth (c : M) (u : FourSpace) :
    ContMDiffOn I4 I4.tangent ∞
      (fun z => (⟨(chartAt FourSpace c).symm z,
        mfderiv I4 I4 (chartAt FourSpace c).symm z u⟩ : TangentBundle I4 M))
      (chartAt FourSpace c).target := by
  have hphi : ContMDiffOn I4 I4 ∞ (chartAt FourSpace c).symm
      (chartAt FourSpace c).target := contMDiffOn_chart_symm
  have ht := hphi.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
    (chartAt FourSpace c).open_target.uniqueMDiffOn
  have hv : ContMDiff I4 I4.tangent ∞
      (fun z => (⟨z, u⟩ : TangentBundle I4 FourSpace)) := by
    exact contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hcomp := ht.comp hv.contMDiffOn (fun z hz => hz)
  apply hcomp.congr
  intro z hz
  exact congrArg (fun L : TangentSpace I4 z →L[ℝ]
      TangentSpace I4 ((chartAt FourSpace c).symm z) =>
        (⟨(chartAt FourSpace c).symm z, L u⟩ : TangentBundle I4 M))
    (mfderivWithin_of_isOpen (chartAt FourSpace c).open_target hz).symm

theorem metricInChart_contDiffOn (g : SmoothMetric M) (c : M) (i j : Fin 4) :
    ContDiffOn ℝ ∞ (fun z => metricInChart g c z i j) (chartAt FourSpace c).target := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hi := chart_inverse_vector_smooth c (coordinateVector i)
  have hj := chart_inverse_vector_smooth c (coordinateVector j)
  have hinner := hi.inner_bundle hj
  exact hinner.contDiffOn

theorem metricInChart_contDiffAt (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => metricInChart g c w i j) z :=
  (metricInChart_contDiffOn g c i j).contDiffAt
    ((chartAt FourSpace c).open_target.mem_nhds hz)

private theorem matrix_det_smooth_at (A : FourSpace → Mat4) (z : FourSpace)
    (hA : ∀ i j, ContDiffAt ℝ ∞ (fun w => A w i j) z) :
    ContDiffAt ℝ ∞ (fun w => (A w).det) z := by
  simp only [Matrix.det_apply']
  apply ContDiffAt.sum
  intro σ _
  exact contDiffAt_const.mul (contDiffAt_prod fun i _ => hA (σ i) i)

private theorem matrix_inverse_entry_smooth_at (A : FourSpace → Mat4) (z : FourSpace)
    (hA : ∀ i j, ContDiffAt ℝ ∞ (fun w => A w i j) z)
    (hdet : (A z).det ≠ 0) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => (A w)⁻¹ i j) z := by
  have hinv : ContDiffAt ℝ ∞ (fun w => ((A w).det)⁻¹) z :=
    (matrix_det_smooth_at A z hA).inv hdet
  have hadj : ContDiffAt ℝ ∞ (fun w => (A w).adjugate i j) z := by
    simp only [Matrix.adjugate_apply]
    apply matrix_det_smooth_at
    intro r t
    by_cases hr : r = j
    · subst r
      simpa only [Matrix.updateRow_self] using
        (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : FourSpace => (Pi.single i (1 : ℝ) : Fin 4 → ℝ) t) z)
    · simpa only [Matrix.updateRow_ne hr] using hA r t
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
    using hinv.mul hadj

theorem christoffel_contDiffAt (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (k i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => christoffel g c w k i j) z := by
  have hm := metricInChart_contDiffAt g c z hz
  have hd (a b d : Fin 4) :
      ContDiffAt ℝ ∞ (fun w => partialDeriv (fun v => metricInChart g c v a b) d w) z := by
    exact ((hm a b).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
  unfold christoffel
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro l _
  exact (matrix_inverse_entry_smooth_at (metricInChart g c) z hm hdet k l).mul
    (((hd j l i).add (hd i l j)).sub (hd i j l))

theorem metricInChart_inv_contDiffAt (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => (metricInChart g c w)⁻¹ i j) z :=
  matrix_inverse_entry_smooth_at (metricInChart g c) z
    (metricInChart_contDiffAt g c z hz) hdet i j

end
end PositiveEinsteinFour.Geometry

end OAI
