import OAI.Analysis.CircleDomains.Sobolev.RectanglePoincare
import OAI.Analysis.CircleDomains.Sobolev.ProductAverage

namespace OAI

/-! The L1 rectangular Poincare estimate, in normalized-average form. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma rectangle_mean_oscillation {f Gx Gy : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hab : a < b) (hcd : c < d)
    (hf : Integrable f ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hGx : Integrable Gx ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hGy : Integrable Gy ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hfx : ∀ᵐ t ∂volume.restrict (Icc c d), ∀ s ∈ Icc a b, ∀ w ∈ Icc a b,
      (∫ r in s..w, Gx (r,t)) = f (w,t)-f (s,t))
    (hfy : ∀ᵐ s ∂volume.restrict (Icc a b), ∀ t ∈ Icc c d, ∀ w ∈ Icc c d,
      (∫ r in t..w, Gy (s,r)) = f (s,w)-f (s,t)) :
    (⨍ y in Icc c d, ⨍ x in Icc a b,
      |f (x,y)-(⨍ s in Icc a b, ⨍ t in Icc c d, f (s,t))|) ≤
      (⨍ y in Icc c d, ∫ x in Icc a b, |Gx (x,y)|) +
      (⨍ x in Icc a b, ∫ y in Icc c d, |Gy (x,y)|) := by
  let : NeZero ((volume : Measure ℝ).restrict (Icc a b)) :=
    ⟨volume_restrict_Icc_ne_zero hab⟩
  let : NeZero ((volume : Measure ℝ).restrict (Icc c d)) :=
    ⟨volume_restrict_Icc_ne_zero hcd⟩
  apply iterated_average_row_bound (hf.sub (integrable_const _)).abs
    hGx.abs.integral_prod_right
  filter_upwards [rectangle_ae_mean_bound hab hcd hf hGx hGy hfx hfy] with y hy
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hy x hx

end CircleDomainRigidity

end

end OAI
