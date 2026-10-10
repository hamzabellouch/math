import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Angular.InnerNormalizedOfClose
import OAI.MeasureTheory.FalconerCompletion.Fourier.MinimalMask

namespace OAI

/-! Dyadic shells and prefix decompositions. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory PlanarFalconer _root_.OAI.GraphLiteralSupport.Attempt4FullFar
open scoped ContDiff Topology
variable {d : ℕ}
namespace PositiveDistanceState
variable (e : PositiveDistanceState d)

noncomputable def prefixCutoff : EuclideanSpace ℝ (Fin d) → ℂ :=
  separatedCutoff e.a (fun j => (pathIndex e.X j:ℤ)) (fun j => (pathIndex e.Y j:ℤ))

lemma prefixCutoff_contDiff : ContDiff ℝ ∞ e.prefixCutoff := separatedCutoff_contDiff _ _ _
lemma prefixCutoff_norm_le (w : EuclideanSpace ℝ (Fin d)) : ‖e.prefixCutoff w‖≤1 :=
  separatedCutoff_norm_le _ _ _ w

lemma ae_prefixCutoff_local [SFinite e.ρ] {K : ℝ} (hK : 32*(d+1:ℝ)≤K)
    (hX : e.X.length=e.a) (hY : e.Y.length=e.a)
    (hs : farSeparatedGridND e.a K (fun j => (pathIndex e.X j:ℤ)) (fun j => (pathIndex e.Y j:ℤ))) :
    ∀ᵐ z ∂e.cellPair,
      e.prefixCutoff =ᶠ[𝓝 ((dist z.1 z.2)⁻¹ • (z.1-z.2))] (fun _ => 1) ∧
      e.prefixCutoff =ᶠ[𝓝 (-((dist z.1 z.2)⁻¹ • (z.1-z.2)))] (fun _ => 0) := by
  filter_upwards [e.ae_cellPair_mem] with z hz
  have hx : z.1∈Attempt4FullFar.ambientGridCell e.a (fun j => (pathIndex e.X j:ℤ)) := by
    have hx := hz.1
    change z.1∈Attempt4FullFar.ambientGridCell e.X.length (fun j => (pathIndex e.X j:ℤ)) at hx
    rwa [hX] at hx
  have hy : z.2∈Attempt4FullFar.ambientGridCell e.a (fun j => (pathIndex e.Y j:ℤ)) := by
    have hy := hz.2
    change z.2∈Attempt4FullFar.ambientGridCell e.Y.length (fun j => (pathIndex e.Y j:ℤ)) at hy
    rwa [hY] at hy
  simpa only [prefixCutoff,radialVector,dist_eq_norm] using separatedCutoff_local hK hs hx hy

end PositiveDistanceState

lemma uniform_prefixCutoff_derivatives (K : ℝ) :
    ∃ C : ℕ → ℝ, (∀ m, 0≤C m) ∧ ∀ (e : PositiveDistanceState d),
      farSeparatedGridND e.a K (fun j => (pathIndex e.X j:ℤ)) (fun j => (pathIndex e.Y j:ℤ)) →
      ∀ m w, ‖w‖=1 → ‖iteratedFDeriv ℝ m e.prefixCutoff w‖≤C m := by
  obtain ⟨C,hC,h⟩ := uniform_separatedCutoff_derivatives (d:=d) K
  exact ⟨C,hC,fun e hs m w hw => h _ _ _ hs m w hw⟩

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
