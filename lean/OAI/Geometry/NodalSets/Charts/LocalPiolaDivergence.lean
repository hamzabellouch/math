import OAI.Geometry.NodalSets.Charts.AbsolutePiola
import OAI.Geometry.NodalSets.Elliptic.CompactSmoothExtension

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

lemma local_absolutePiola_divergence (F : Coord → Coord) {U : Set Coord}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (V : Fin 4 → Coord → ℂ)
    (x : Coord) (hx : x ∈ U) (hV : ∀ a, DifferentiableAt ℝ (V a) (F x))
    (hdet : (jacobian F x).det ≠ 0) :
    complexDivergence (absolutePiola F V) x =
      ((|(jacobian F x).det| : ℝ) : ℂ) * complexDivergence V (F x) := by
  obtain ⟨G,hG,_,_,hge⟩ := compact_smooth_extension isCompact_singleton hU
    (singleton_subset_iff.mpr hx) F hF
  have he := hge x (mem_singleton x)
  have hj : jacobian G =ᶠ[𝓝 x] jacobian F := by
    filter_upwards [he.fderiv (𝕜 := ℝ)] with y hy
    unfold jacobian
    rw [hy]
  have hp (i : Fin 4) : absolutePiola G V i =ᶠ[𝓝 x] absolutePiola F V i := by
    filter_upwards [he,hj] with y hy hjy
    simp only [absolutePiola,signedPiola,hy,hjy]
  have hdiv : complexDivergence (absolutePiola G V) x =
      complexDivergence (absolutePiola F V) x := by
    unfold complexDivergence coordPartial
    apply Finset.sum_congr rfl
    intro i _
    rw [(hp i).fderiv_eq]
  have h := absolutePiola_divergence G hG V x (by simpa only [he.eq_of_nhds] using hV)
    (by simpa only [hj.eq_of_nhds] using hdet)
  simpa only [hdiv,hj.eq_of_nhds,he.eq_of_nhds] using h

end
end Yau.Geometry

end OAI
