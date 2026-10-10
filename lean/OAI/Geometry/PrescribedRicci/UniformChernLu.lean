import Mathlib
import OAI.Geometry.PrescribedRicci.ChernLuAlgebra
import OAI.Geometry.PrescribedRicci.ChernLuDifferential
import OAI.Geometry.PrescribedRicci.CurvatureCompactBounds
import OAI.Geometry.PrescribedRicci.KaehlerLogTrace
import OAI.Geometry.PrescribedRicci.MatrixComponentBounds
import OAI.Geometry.PrescribedRicci.TraceEntryBounds
import OAI.Geometry.PrescribedPotential.VolumePath

namespace OAI

/-! Uniform Chern Lu. -/

section

 

noncomputable section
open Matrix Filter Set Topology
open scoped ContDiff ComplexOrder MatrixOrder
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

lemma volumePath_ricci_bound (g : KaehlerMetric A) (line : SemipositiveAnticanonicalMetric A)
    {t b : ℝ} {φ : SmoothRealFunction A} (hp : g.PositivePotential φ)
    (heq : ∀ x, (g.logRatio (g.deform φ hp)).value x =
      t*(prescribedForcing g line).value x+b)
    (ht : t ∈ Icc (0:ℝ) 1) (q : Fin A.count) {z : Coordinates d}
    (hz : z ∈ (A.chart q).target) {M : ℝ} (hM : 0 ≤ M)
    (hB : g.BackgroundComponentBound (prescribedForcing g line) q z M) (i j : Fin d) :
    ‖(g.deform φ hp).curvatureRicci q z i j‖ ≤ 2*M := by
  rw [g.volumePath_ricci line hp heq q hz]
  change ‖g.curvatureRicci q z i j-(t:ℂ)*(prescribedForcing g line).hessian q z i j‖ ≤ _
  calc
    _ ≤ ‖g.curvatureRicci q z i j‖+‖(t:ℂ)*(prescribedForcing g line).hessian q z i j‖ := norm_sub_le _ _
    _ ≤ M+M := add_le_add (hB.2.2.1 i j) (by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_left (hB.2.2.2.1 i j) ht.1).trans
        (by nlinarith [ht.2]))
    _ = _ := by ring

lemma chernLu_of_background_bound (g : KaehlerMetric A) (line : SemipositiveAnticanonicalMetric A)
    (hd : 0 < d) {t b : ℝ} {φ : SmoothRealFunction A} (hp : g.PositivePotential φ)
    (heq : ∀ x, (g.logRatio (g.deform φ hp)).value x =
      t*(prescribedForcing g line).value x+b)
    (ht : t ∈ Icc (0:ℝ) 1) (q : Fin A.count) {z : Coordinates d}
    (hz : z ∈ (A.chart q).target) {M : ℝ} (hM : 0 ≤ M)
    (hB : g.BackgroundComponentBound (prescribedForcing g line) q z M) :
    -((d:ℝ)^4*M^3+2*(d:ℝ)^4*M^4)*((g.deform φ hp).traceMetric g).localExpression q z ≤
      ((g.deform φ hp).laplacian ((g.deform φ hp).logTrace g hd)).localExpression q z := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let h := g.deform φ hp
  let S := (h.traceMetric g).localExpression q z
  have hS : 0 < S := h.traceMetric_pos g hd ((A.chart q).symm z)
  have hi (i j : Fin d) : ‖(h.matrix q z)⁻¹ i j‖ ≤ M*S := by
    dsimp [S]
    rw [h.traceMetric_local g q hz]
    exact MongeAmpere.entry_le_relative_trace _ _ (h.positive q z hz).inv (g.positive q z hz)
      hM (fun i => (Complex.re_le_norm _).trans (hB.2.1 i i)) i j
  have hcurv : h.targetCurvatureTerm g q z ≤ ((d:ℝ)^4*M^3)*S^2 := by
    change (∑ a, ∑ b, (h.matrix q z)⁻¹ a b*((h.matrix q z)⁻¹*g.curvatureMatrix q z b a).trace).re ≤ _
    apply (Complex.re_le_norm _).trans
    have hh := MongeAmpere.contracted_curvature_bound (mul_nonneg hM hS.le) hi hB.2.2.2.2
    simp only [Fintype.card_fin] at hh
    convert hh using 1
    first | rfl | ring
  have hricci : -(2*(d:ℝ)^4*M^4)*S^2 ≤ h.sourceRicciTerm g q z := by
    have hh := MongeAmpere.trace_four_entry_bound (mul_nonneg hM hS.le)
      (mul_nonneg (by norm_num : (0:ℝ)≤2) hM) (mul_nonneg hM hS.le)
      hi (g.volumePath_ricci_bound line hp heq ht q hz hM hB) hi hB.1
    simp only [Fintype.card_fin] at hh
    have hh' : ‖((h.matrix q z)⁻¹*h.curvatureRicci q z*(h.matrix q z)⁻¹*g.matrix q z).trace‖ ≤
        (2*(d:ℝ)^4*M^4)*S^2 := by
      convert hh using 1
      first | rfl | ring
    have hl := (abs_le.mp (Complex.abs_re_le_norm ((h.matrix q z)⁻¹*h.curvatureRicci q z*(h.matrix q z)⁻¹*g.matrix q z).trace)).1
    dsimp [sourceRicciTerm]
    linarith
  exact h.chernLu_of_component_bounds g hd q hz hcurv hricci

variable [T2Space X] [CompactSpace X]

lemma uniform_chernLu (g : KaehlerMetric A) (line : SemipositiveAnticanonicalMetric A)
    (hd : 0 < d) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (t b : ℝ) (φ : SmoothRealFunction A) (hp : g.PositivePotential φ),
    (∀ x, (g.logRatio (g.deform φ hp)).value x = t*(prescribedForcing g line).value x+b) →
    t ∈ Icc (0:ℝ) 1 → ∀ x,
    -C*((g.deform φ hp).traceMetric g).value x ≤
      ((g.deform φ hp).laplacian ((g.deform φ hp).logTrace g hd)).value x := by
  obtain ⟨M,hM,hB⟩ := g.compact_background_bounds (prescribedForcing g line)
  refine ⟨(d:ℝ)^4*M^3+2*(d:ℝ)^4*M^4,by positivity,?_⟩
  intro t b φ hp heq ht x
  obtain ⟨q,hq⟩ := exists_partition_chart (A:=A) x
  have hx := chartPartition_support q hq
  have hh := g.chernLu_of_background_bound line hd hp heq ht q ((A.chart q).mapsTo hx)
    (by linarith) (hB q x hq)
  simpa only [SmoothRealFunction.localExpression,Function.comp_apply,(A.chart q).left_inv hx] using hh

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI
