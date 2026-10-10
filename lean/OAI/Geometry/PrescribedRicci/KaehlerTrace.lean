import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalOperator

namespace OAI

/-! Kaehler Trace. -/

noncomputable section
open Matrix Filter Set Topology
open scoped ContDiff ComplexOrder MatrixOrder Matrix.Norms.Elementwise
namespace MongeAmpere
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma trace_mul_pos [Nonempty n] {H G : Matrix n n ℂ}
    (hH : H.PosDef) (hG : G.PosDef) : 0 < (H*G).trace.re := by
  let S := CFC.sqrt H
  have hS : S.PosSemidef := (CFC.sqrt_nonneg H).posSemidef
  have hs : S*S=H := by simpa [S,pow_two] using CFC.sq_sqrt H hH.posSemidef.nonneg
  have hSn : S.det ≠ 0 := by
    intro hz
    have he := congrArg Matrix.det hs
    rw [det_mul,hz,zero_mul] at he
    exact hH.det_pos.ne' he.symm
  have hp := hG.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_det_ne_zero hSn)
  have ht := (Complex.pos_iff.mp hp.trace_pos).1
  have he : (Sᴴ*G*S).trace = (H*G).trace := by
    rw [hS.isHermitian.eq,trace_mul_cycle,hs]
  rwa [he] at ht

end MongeAmpere
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

lemma traceMetric_compatibility (g h : KaehlerMetric A) (i j : Fin A.count)
    {x : X} (hi : x ∈ (A.chart i).source) (hj : x ∈ (A.chart j).source) :
    ((g.matrix i (A.chart i x))⁻¹*h.matrix i (A.chart i x)).trace =
      ((g.matrix j (A.chart j x))⁻¹*h.matrix j (A.chart j x)).trace := by
  let D := A.derivativeMatrix i j x
  have hD : IsUnit D.det := g.transition_det_isUnit i j hi hj
  have hs : IsUnit Dᴴ.det := by rw [det_conjTranspose]; exact hD.star
  rw [g.compatibility i j x hi hj,h.compatibility i j x hi hj]
  change ((Dᴴ*g.matrix j (A.chart j x)*D)⁻¹*(Dᴴ*h.matrix j (A.chart j x)*D)).trace = _
  rw [Matrix.mul_inv_rev,Matrix.mul_inv_rev]
  simp only [mul_assoc,nonsing_inv_mul_cancel_left Dᴴ _ hs]
  have he : D⁻¹ * ((g.matrix j (A.chart j x))⁻¹ * (h.matrix j (A.chart j x) * D)) =
      D⁻¹ * ((g.matrix j (A.chart j x))⁻¹ * h.matrix j (A.chart j x)) * D := by simp only [mul_assoc]
  rw [he, trace_mul_cycle, mul_nonsing_inv D hD, one_mul]

def traceMetricValue (g h : KaehlerMetric A) (x : X) : ℝ :=
  (((g.matrix (A.covers x).choose (A.chart (A.covers x).choose x))⁻¹)*
    h.matrix (A.covers x).choose (A.chart (A.covers x).choose x)).trace.re

lemma traceMetricValue_local (g h : KaehlerMetric A) (i : Fin A.count)
    {x : X} (hx : x ∈ (A.chart i).source) :
    g.traceMetricValue h x = ((g.matrix i (A.chart i x))⁻¹*h.matrix i (A.chart i x)).trace.re :=
  congrArg Complex.re (g.traceMetric_compatibility h _ i (A.covers x).choose_spec hx)

lemma traceMetric_local_smooth (g h : KaehlerMetric A) (i : Fin A.count) :
    ContDiffOn ℝ ∞ (fun z => ((g.matrix i z)⁻¹*h.matrix i z).trace.re) (A.chart i).target := by
  apply Complex.reCLM.contDiff.comp_contDiffOn
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply]
  apply ContDiffOn.sum
  intro j _
  apply ContDiffOn.sum
  intro k _
  exact (contDiffOn_pi.mp (contDiffOn_pi.mp (MatrixSmoothGeneral.inverse (g.smooth i)
    (fun z hz => (g.positive i z hz).det_pos.ne')) j) k).mul
    (contDiffOn_pi.mp (contDiffOn_pi.mp (h.smooth i) k) j)

def traceMetric (g h : KaehlerMetric A) : SmoothRealFunction A where
  value := g.traceMetricValue h
  smooth i := by
    apply (g.traceMetric_local_smooth h i).congr
    intro z hz
    dsimp only [Function.comp_apply]
    rw [g.traceMetricValue_local h i ((A.chart i).mapsTo_symm hz),(A.chart i).right_inv hz]

lemma traceMetric_local (g h : KaehlerMetric A) (i : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart i).target) :
    (g.traceMetric h).localExpression i z = ((g.matrix i z)⁻¹*h.matrix i z).trace.re := by
  change g.traceMetricValue h ((A.chart i).symm z) = _
  rw [g.traceMetricValue_local h i ((A.chart i).mapsTo_symm hz),(A.chart i).right_inv hz]

lemma traceMetric_pos (g h : KaehlerMetric A) (hd : 0 < d) (x : X) :
    0 < (g.traceMetric h).value x := by
  let : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  obtain ⟨i,hi⟩ := A.covers x
  change 0 < g.traceMetricValue h x
  rw [g.traceMetricValue_local h i hi]
  exact MongeAmpere.trace_mul_pos (g.positive i _ ((A.chart i).mapsTo hi)).inv
    (h.positive i _ ((A.chart i).mapsTo hi))

lemma laplacian_deform (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (hp : g.PositivePotential φ) (x : X) :
    ((g.deform φ hp).laplacian φ).value x = d-((g.deform φ hp).traceMetric g).value x := by
  obtain ⟨i,hi⟩ := A.covers x
  let H := (g.deform φ hp).matrix i (A.chart i x)
  have hH : IsUnit H.det := isUnit_iff_ne_zero.mpr ((g.deform φ hp).positive i _ ((A.chart i).mapsTo hi)).det_pos.ne'
  change (g.deform φ hp).laplacianValue φ x = (d:ℝ)-(g.deform φ hp).traceMetricValue g x
  rw [(g.deform φ hp).laplacianValue_local φ i hi,(g.deform φ hp).traceMetricValue_local g i hi]
  unfold linearizedMongeAmpere
  have he : φ.hessian i (A.chart i x) = H-g.matrix i (A.chart i x) := by dsimp [H,deform]; abel
  rw [he,mul_sub,Matrix.nonsing_inv_mul _ hH,trace_sub,Complex.sub_re,trace_one]
  simp

end Anticanonical.SourceSmooth.KaehlerMetric

end

end OAI
