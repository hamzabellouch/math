import Mathlib
import OAI.Geometry.PrescribedPotential.PositivePotentialLinearization
import OAI.Geometry.PrescribedRicci.LocalizedPathData
import OAI.Geometry.PrescribedRicci.PositivePathOpenness

namespace OAI

/-! Path Localized Density. -/

section

 
noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff SchwartzMap Classical ComplexOrder MatrixOrder Matrix.Norms.Elementwise
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
  {g : KaehlerMetric A}

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
lemma metric_det_euclidean_smooth (g : KaehlerMetric A) (q : Fin A.count) :
    ContDiffOn ℝ ∞ (fun y : EC d => (g.matrix q (coordinateEquiv d y)).det)
      (A.euclideanChart q).target := by
  simp only [Matrix.det_apply']
  apply ContDiffOn.sum
  intro π _
  apply contDiffOn_const.mul
  apply contDiffOn_prod
  intro i _
  exact contDiffOn_pi.mp (contDiffOn_pi.mp (GluingData.metric_euclidean_smooth g q) (π i)) i

def cutPathDensity (g : KaehlerMetric A) (line : SemipositiveAnticanonicalMetric A)
    (q : Fin A.count) (σ : ChartCutoff (A.euclideanChart q).target)
    (z : g.NormalizedPathSolution line) : 𝓢(EC d,ℂ) :=
  localize A q
    (cutoffGlobal q (σ.mulOn (A.euclideanChart q).open_target (metric_det_euclidean_smooth g q)))
    (cutoffGlobal_support q _)
    ((RealSmooth.ofReal (prescribedForcing g line)).expAffine z.time z.constant).val

omit [ConnectedSpace X] in
lemma cutPathDensity_apply (line : SemipositiveAnticanonicalMetric A)
    (q : Fin A.count) (σ : ChartCutoff (A.euclideanChart q).target)
    (z : g.NormalizedPathSolution line) (y : EC d) :
    cutPathDensity g line q σ z y = σ y*(g.matrix q (coordinateEquiv d y)).det*
      (Real.exp (z.time*(prescribedForcing g line).value ((A.euclideanChart q).symm y)+z.constant):ℂ) := by
  rw [cutPathDensity,localize_cutoff_product]
  rfl

lemma cutPathDensity_uniform (D : GluingData g ι) (line : SemipositiveAnticanonicalMetric A)
    (q : Fin A.count) (σ : ChartCutoff (A.euclideanChart q).target) (k : ℕ) :
    UniformSobolev (k:ℝ) (cutPathDensity g line q σ) :=
  D.uniform_localize k _ (D.volumePath_forcing_uniform line k) q _ _

omit [ConnectedSpace X] in
lemma path_determinant_equation (line : SemipositiveAnticanonicalMetric A)
    (z : g.NormalizedPathSolution line) (q : Fin A.count) {y : EC d}
    (hy : y ∈ (A.euclideanChart q).target) :
    ((g.deform z.potential z.positive).matrix q (coordinateEquiv d y)).det =
      (g.matrix q (coordinateEquiv d y)).det *
        (Real.exp (z.time*(prescribedForcing g line).value ((A.euclideanChart q).symm y)+z.constant):ℂ) := by
  let x := (A.euclideanChart q).symm y
  have hyt : coordinateEquiv d y ∈ (A.chart q).target := by simpa using hy
  have hx : x ∈ (A.chart q).source := by simpa [x] using (A.euclideanChart q).symm.mapsTo hy
  have hxy : A.chart q x = coordinateEquiv d y :=
    (A.chart q).right_inv hyt
  have hp := g.potentialDensity_pos z.potential z.positive x
  have heq := z.equation x
  rw [g.logRatio_eq_log_density z.potential z.positive x] at heq
  have he : (g.potentialDensity z.potential).value x =
      Real.exp (z.time*(prescribedForcing g line).value x+z.constant) := by
    rw [← heq,Real.exp_log hp]
  have hd := g.potentialDensity_complex z.potential q hx
  rw [hxy,he] at hd
  change (Real.exp (_):ℂ) = _/_ at hd
  have hn : (g.matrix q (coordinateEquiv d y)).det ≠ 0 := (g.positive q _ hyt).det_pos.ne'
  rw [eq_div_iff hn] at hd
  exact hd.symm.trans (mul_comm _ _)

omit [ConnectedSpace X] in
lemma cutPathDensity_germ (line : SemipositiveAnticanonicalMetric A)
    (q : Fin A.count) (σ : ChartCutoff (A.euclideanChart q).target)
    (z : g.NormalizedPathSolution line) {y : EC d} (hy : y ∈ (A.euclideanChart q).target)
    (hσ : (σ : EC d → ℂ) =ᶠ[𝓝 y] fun _ => 1) :
    (fun x => (show Matrix (Fin d) (Fin d) ℂ from fun i j =>
      cutMetric (g.deform z.potential z.positive) q σ i j x).det) =ᶠ[𝓝 y]
      cutPathDensity g line q σ z := by
  filter_upwards [hσ,(A.euclideanChart q).open_target.mem_nhds hy] with x hx hxt
  have hH : (show Matrix (Fin d) (Fin d) ℂ from fun i j =>
      cutMetric (g.deform z.potential z.positive) q σ i j x) =
      (g.deform z.potential z.positive).matrix q (coordinateEquiv d x) := by
    ext i j
    rw [cutMetric_apply,hx,one_mul]
  rw [hH,cutPathDensity_apply,hx,one_mul]
  exact path_determinant_equation line z q hxt
end GlobalElliptic

end
end

end OAI
