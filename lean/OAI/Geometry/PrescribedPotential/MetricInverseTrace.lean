import Mathlib
import OAI.Geometry.PrescribedPotential.InverseTraceFunction
import OAI.Geometry.PrescribedPotential.MatrixFrameNormalization

namespace OAI

/-! Metric Inverse Trace. -/

section

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
namespace KaehlerMetric

lemma derivativeMatrix_isUnit (g : KaehlerMetric A) (i j : Fin A.count) {x : X}
    (hi : x ∈ (A.chart i).source) (hj : x ∈ (A.chart j).source) :
    IsUnit (A.derivativeMatrix i j x) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  intro he
  have hh := congrArg Matrix.det (g.compatibility i j x hi hj)
  rw [Matrix.det_mul,he,mul_zero] at hh
  exact (ne_of_gt (g.positive i _ ((A.chart i).mapsTo hi)).det_pos) hh

lemma inverseTrace_compatibility (g G : KaehlerMetric A) (i j : Fin A.count) {x : X}
    (hi : x ∈ (A.chart i).source) (hj : x ∈ (A.chart j).source) :
    KaehlerCalculus.inverseTrace (g.matrix i) (G.matrix i) (A.chart i x) =
      KaehlerCalculus.inverseTrace (g.matrix j) (G.matrix j) (A.chart j x) := by
  unfold KaehlerCalculus.inverseTrace
  rw [g.compatibility i j x hi hj,G.compatibility i j x hi hj,
    KaehlerCalculus.matrix_inverse_trace_congruence _ _ _ (g.derivativeMatrix_isUnit i j hi hj)]

def inverseTraceValue (g G : KaehlerMetric A) (x : X) : ℝ :=
  let i := (A.covers x).choose
  KaehlerCalculus.inverseTrace (g.matrix i) (G.matrix i) (A.chart i x)

lemma inverseTraceValue_local (g G : KaehlerMetric A) (i : Fin A.count) {x : X}
    (hi : x ∈ (A.chart i).source) :
    g.inverseTraceValue G x = KaehlerCalculus.inverseTrace (g.matrix i) (G.matrix i) (A.chart i x) := by
  exact g.inverseTrace_compatibility G _ i (A.covers x).choose_spec hi

def inverseTrace (g G : KaehlerMetric A) : SmoothRealFunction A where
  value := g.inverseTraceValue G
  smooth i := by
    apply (KaehlerCalculus.inverseTrace_smooth (A.chart i).open_target (g.smooth i)
      (g.positive i) (G.smooth i)).congr
    intro z hz
    dsimp only [Function.comp_apply]
    rw [g.inverseTraceValue_local G i ((A.chart i).mapsTo_symm hz),(A.chart i).right_inv hz]

lemma inverseTrace_local (g G : KaehlerMetric A) (i : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart i).target) :
    (g.inverseTrace G).localExpression i z = KaehlerCalculus.inverseTrace (g.matrix i) (G.matrix i) z := by
  change g.inverseTraceValue G ((A.chart i).symm z) = _
  rw [g.inverseTraceValue_local G i ((A.chart i).mapsTo_symm hz),(A.chart i).right_inv hz]

lemma inverseTrace_positive [Nonempty (Fin d)] (g G : KaehlerMetric A) (x : X) :
    0 < (g.inverseTrace G).value x := by
  obtain ⟨i,hi⟩ := A.covers x
  change 0 < g.inverseTraceValue G x
  rw [g.inverseTraceValue_local G i hi]
  exact KaehlerCalculus.inverseTrace_pos (g.positive i _ ((A.chart i).mapsTo hi))
    (G.positive i _ ((A.chart i).mapsTo hi))
end KaehlerMetric
end Anticanonical.SourceSmooth

end
end

end OAI
