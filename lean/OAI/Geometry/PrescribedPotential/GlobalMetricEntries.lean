import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalTransport
import OAI.Geometry.PrescribedPotential.PatchCutoffs

namespace OAI

/-! Global Metric Entries. -/

section

 
noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff SchwartzMap Classical ComplexOrder Matrix.Norms.Elementwise
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]

def chartFunction (q : Fin A.count) (κ : ChartCutoff (A.euclideanChart q).target)
    (f : EC d → ℂ) (hf : ContDiffOn ℝ ∞ f (A.euclideanChart q).target) : Smooth A :=
  cutoffGlobal q (κ.mulOn (A.euclideanChart q).open_target hf)

lemma chartFunction_apply (q : Fin A.count) (κ : ChartCutoff (A.euclideanChart q).target)
    (f : EC d → ℂ) (hf : ContDiffOn ℝ ∞ f (A.euclideanChart q).target)
    {x : X} (hx : x ∈ (A.euclideanChart q).source) :
    chartFunction q κ f hf x = κ (A.euclideanChart q x) * f (A.euclideanChart q x) := by
  change (if x ∈ (A.euclideanChart q).source then _ else 0) = _
  rw [ite_eq_left hx]
  rfl

namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

omit [T2Space X] in
lemma metric_euclidean_smooth (g : KaehlerMetric A) (q : Fin A.count) :
    ContDiffOn ℝ ∞ (fun y : EC d => g.matrix q (coordinateEquiv d y))
      (A.euclideanChart q).target := by
  rw [ComplexAtlas.euclideanChart_target]
  exact (g.smooth q).comp (coordinateEquiv d).contDiff.contDiffOn (fun _ h => h)

omit [T2Space X] in
lemma inverseDet_euclidean_smooth (g : KaehlerMetric A) (q : Fin A.count) :
    ContDiffOn ℝ ∞ (fun y : EC d => (g.matrix q (coordinateEquiv d y)).det⁻¹)
      (A.euclideanChart q).target := by
  have hd : ContDiffOn ℝ ∞ (fun y : EC d => (g.matrix q (coordinateEquiv d y)).det)
      (A.euclideanChart q).target := by
    simp only [Matrix.det_apply']
    apply ContDiffOn.sum
    intro σ _
    apply contDiffOn_const.mul
    apply contDiffOn_prod
    intro j _
    exact contDiffOn_pi.mp (contDiffOn_pi.mp (metric_euclidean_smooth g q) (σ j)) j
  apply hd.inv
  intro y hy
  exact ne_of_gt (g.positive q (coordinateEquiv d y) (by simpa using hy)).det_pos

def metricEntry (p : ι) (i j : Fin d) : Smooth A :=
  chartFunction (D.patch p).index (D.cutoff p)
    (fun y => g.matrix (D.patch p).index (coordinateEquiv d y) i j)
    (contDiffOn_pi.mp (contDiffOn_pi.mp (metric_euclidean_smooth g (D.patch p).index) i) j)

def inverseDet (p : ι) : Smooth A :=
  chartFunction (D.patch p).index (D.cutoff p)
    (fun y => (g.matrix (D.patch p).index (coordinateEquiv d y)).det⁻¹)
    (inverseDet_euclidean_smooth g (D.patch p).index)

def determinantWeight (p : ι) : Smooth A := (D.localizers.weight p).mul (D.inverseDet p)

omit [T2Space X] in
lemma patch_source (p : ι) {x : X} (hx : x ∈ tsupport (D.localizers.weight p : X → ℂ)) :
    x ∈ (A.euclideanChart (D.patch p).index).source := by
  have hh := D.localizers.support_sub p hx
  rwa [D.index_eq] at hh

lemma metricEntry_apply (p : ι) (i j : Fin d) {x : X}
    (hx : x ∈ tsupport (D.localizers.weight p : X → ℂ)) :
    D.metricEntry p i j x = g.matrix (D.patch p).index (A.chart (D.patch p).index x) i j := by
  rw [metricEntry, chartFunction_apply _ _ _ _ (D.patch_source p hx), D.cutoff_one p x hx, one_mul,
    ComplexAtlas.euclideanChart_apply, ContinuousLinearEquiv.apply_symm_apply]

lemma inverseDet_apply (p : ι) {x : X}
    (hx : x ∈ tsupport (D.localizers.weight p : X → ℂ)) :
    D.inverseDet p x = (g.matrix (D.patch p).index (A.chart (D.patch p).index x)).det⁻¹ := by
  rw [inverseDet, chartFunction_apply _ _ _ _ (D.patch_source p hx), D.cutoff_one p x hx, one_mul,
    ComplexAtlas.euclideanChart_apply, ContinuousLinearEquiv.apply_symm_apply]

lemma determinantWeight_apply (p : ι) {x : X}
    (hx : x ∈ tsupport (D.localizers.weight p : X → ℂ)) :
    D.determinantWeight p x = D.localizers.weight p x *
      (g.matrix (D.patch p).index (A.chart (D.patch p).index x)).det⁻¹ := by
  change D.localizers.weight p x * D.inverseDet p x = _
  rw [D.inverseDet_apply p hx]

lemma determinantWeight_zero (p : ι) {x : X} (hx : D.localizers.weight p x = 0) :
    D.determinantWeight p x = 0 := by
  change D.localizers.weight p x * _ = 0
  rw [hx, zero_mul]

end GluingData
end GlobalElliptic

end
end

end OAI
