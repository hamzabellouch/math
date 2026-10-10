import Mathlib
import OAI.Geometry.Borsuk.LocalParity.RegularBase
import OAI.Geometry.Borsuk.LocalParity.ChartRegular
import OAI.Geometry.Borsuk.Support.LocalMix

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped RealInnerProductSpace
section RegularModel
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin (k+1))
local notation "W" => EuclideanSpace ℝ (Fin k)
lemma Admissible.regular_model_data {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) {w c : E} (hw : ‖w‖ = 1) (hc : ‖c‖ = 1)
    (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪w,e v⟫ = 0) (hes : ∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u)
    (hwc : 0 < ⟪w,c⟫) {z : W} (hcval : f c = facetPoint a z)
    (hr : ∀ v, baseCoordinates f w e a v = z → (fderiv ℝ (baseCoordinates f w e a) v).det ≠ 0) :
    ∃ (d : W →ₗᵢ[ℝ] E) (D : W ≃L[ℝ] W) (δ : ℝ),
      (∀ v, ⟪c,d v⟫ = 0) ∧ (∀ u, ⟪c,u⟫ = 0 → ∃ v, d v = u) ∧ 0 < δ ∧
      ∀ u : E, ‖u‖ = 1 → 0 < ⟪c,u⟫ → ‖hemisphereInverse c d u‖ < δ →
        hemisphereInverse c d u ≠ 0 → 0 < ⟪hemisphereInverse c d u,D.symm (facetTail a (f u-f c))⟫ := by
  obtain ⟨d,hd,hds⟩ := orthogonal_frame k hc
  let F : E → W := fun u => facetTail a (f u)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := by
    apply (contDiff_piLp 2).mpr
    intro j
    exact hf.smooth (a j.succ).val
  have hz : baseCoordinates f w e a (hemisphereInverse w e c) = z := by
    ext j
    change f (hemisphereChart w e (hemisphereInverse w e c)) (a j.succ).val = z j
    rw [hemisphereChart_inverse w e hw he hes hc hwc,hcval,facetPoint_apply,simplexPoint_succ]
  have hdet : (fderiv ℝ (baseCoordinates f c d a) 0).det ≠ 0 :=
    hemisphere_transition_regular hw hc e d he hd hes hds hwc F hF (hr _ hz)
  let D : W ≃L[ℝ] W :=
    (fderiv ℝ (baseCoordinates f c d a) 0).toContinuousLinearEquivOfDetNeZero hdet
  have hD : D.toContinuousLinearMap = fderiv ℝ (baseCoordinates f c d a) 0 := by
    exact ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ hdet
  let g : W → W := fun v => baseCoordinates f c d a v - F c
  have hg0 : g 0 = 0 := by
    change F (hemisphereChart c d 0) - F c = 0
    rw [hemisphereChart_zero hc,sub_self]
  have hgd : HasFDerivAt g D.toContinuousLinearMap 0 := by
    rw [hD]
    exact (((hf.baseCoordinates_contDiff hc d hd a).differentiable (by simp) 0).hasFDerivAt).sub_const (F c)
  obtain ⟨δ,hδ,hpos⟩ := regular_inner_positive D hg0 hgd
  refine ⟨d,D,δ,hd,hds,hδ,?_⟩
  intro u hu hcu hδu hv
  have hg : g (hemisphereInverse c d u) = facetTail a (f u-f c) := by
    change F (hemisphereChart c d (hemisphereInverse c d u)) - F c = _
    rw [hemisphereChart_inverse c d hc hd hds hu hcu]
    exact (map_sub (facetTail a) _ _).symm
  rw [← hg]
  exact hpos _ hδu hv
end RegularModel
end BorsukNine

end OAI
