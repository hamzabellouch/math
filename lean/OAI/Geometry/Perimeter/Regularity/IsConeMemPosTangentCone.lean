import OAI.Geometry.Perimeter.Regularity.ConeRadialCap
import OAI.Geometry.Perimeter.Regularity.GeoComposition

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
namespace RPISingularHarnack

theorem isCone_mem_posTangentCone {n : ℕ} {S : Set (Euc n)}
    (hcone : IsCone S) {x : Euc n} (hx : x ∈ S) :
    x ∈ posTangentConeAt S (0 : Euc n) := by
  apply mem_posTangentConeAt_of_frequently_mem
  apply Filter.Eventually.frequently
  filter_upwards [self_mem_nhdsWithin] with r hr
  simpa only [zero_add] using (hcone r hr x).mpr hx

theorem minimizing_cone_supporting_fderiv_eq_zero {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (hcone : IsCone E) {f : Euc n → ℝ}
    (hf : DifferentiableAt ℝ f (0 : Euc n))
    (hmax : IsLocalMaxOn f (perimeterSupport E) (0 : Euc n)) :
    ∀ x ∈ perimeterSupport E, fderiv ℝ f (0 : Euc n) x = 0 := by
  have hc := isCone_perimeterSupport hmin.1 hcone
  have hneg (x : Euc n) (hx : x ∈ perimeterSupport E) :
      fderiv ℝ f (0 : Euc n) x ≤ 0 :=
    hmax.hasFDerivWithinAt_nonpos hf.hasFDerivAt.hasFDerivWithinAt
      (isCone_mem_posTangentCone hc hx)
  have hside : ∀ x ∈ perimeterSupport E,
      0 ≤ inner ℝ x (-gradient f (0 : Euc n)) := by
    intro x hx
    rw [inner_neg_right, real_inner_comm, inner_gradient_left]
    linarith [hneg x hx]
  have hzero := minimizing_cone_support_in_halfspace_plane hn hmin hcone
    (-gradient f (0 : Euc n)) hside
  intro x hx
  have hh := hzero x hx
  rw [inner_neg_right, real_inner_comm, inner_gradient_left] at hh
  linarith

theorem minimizing_cone_supporting_fderiv_zero_of_span {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (hcone : IsCone E) (hspan : Submodule.span ℝ (perimeterSupport E) = ⊤)
    {f : Euc n → ℝ} (hf : DifferentiableAt ℝ f (0 : Euc n))
    (hmax : IsLocalMaxOn f (perimeterSupport E) (0 : Euc n)) :
    fderiv ℝ f (0 : Euc n) = 0 := by
  have hz := minimizing_cone_supporting_fderiv_eq_zero hn hmin hcone hf hmax
  have hker : Submodule.span ℝ (perimeterSupport E) ≤
      LinearMap.ker (fderiv ℝ f (0 : Euc n)).toLinearMap :=
    Submodule.span_le.mpr hz
  rw [hspan] at hker
  ext x
  exact hker (by trivial)

end RPISingularHarnack

end

end OAI
