import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceTimeBlend
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

namespace OAI

/-! Exterior germs of the actual chart blend and an explicit time cutoff. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] {F : M → ℝ}

lemma surfaceTimeBlend_zero (c d : SurfaceTimeChart F) {χ : ℝ → ℝ} {x : M}
    (hx : χ (F x) = 0) : surfaceTimeBlend c d χ x = c.coord x := by
  simp [surfaceTimeBlend,hx]

lemma surfaceTimeBlend_one (c d : SurfaceTimeChart F) {χ : ℝ → ℝ} {x : M}
    (hx : χ (F x) = 1) : surfaceTimeBlend c d χ x = d.coord x := by
  simp [surfaceTimeBlend,hx]

lemma surfaceTimeBlend_axis (c d : SurfaceTimeChart F) {χ : ℝ → ℝ} {x : M} {t : ℝ}
    (hc : c.coord x = ![0,t]) (hd : d.coord x = ![0,t]) :
    surfaceTimeBlend c d χ x = ![0,t] := by
  simp only [surfaceTimeBlend,hc,hd]
  rw [← add_smul]
  simp

lemma surfaceTimeBlend_time (c d : SurfaceTimeChart F) {χ : ℝ → ℝ} {x : M}
    (hc : x ∈ c.coord.source) (hd : x ∈ d.coord.source) :
    surfaceTimeBlend c d χ x 1 = F x := by
  change (1-χ (F x)) * c.coord x 1 + χ (F x) * d.coord x 1 = F x
  rw [c.time x hc,d.time x hd]
  ring

def timeCutoff (l r : ℝ) (t : ℝ) : ℝ := Real.smoothTransition ((t-l)/(r-l))

lemma timeCutoff_smooth (l r : ℝ) : ContDiff ℝ ∞ (timeCutoff l r) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

lemma timeCutoff_mem (l r t : ℝ) : timeCutoff l r t ∈ Icc (0:ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

lemma timeCutoff_zero {l r t : ℝ} (hlr : l < r) (ht : t ≤ l) :
    timeCutoff l r t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_pos.mpr hlr).le

lemma timeCutoff_one {l r t : ℝ} (hlr : l < r) (ht : r ≤ t) :
    timeCutoff l r t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ (sub_pos.mpr hlr)).mpr
  linarith

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
