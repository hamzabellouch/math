import OAI.Analysis.CircleDomains.Sobolev.TensorAverageBound
import OAI.Analysis.CircleDomains.Topology.IntervalPoincare

namespace OAI

/-! Axis-by-axis mean oscillation on actual Euclidean rectangles. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma rectangle_point_mean_bound {f Gx Gy : ℝ × ℝ → ℝ} {a b c d x y : ℝ}
    (hab : a < b) (hcd : c < d)
    (hf : Integrable f ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hGy : Integrable Gy ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hrow : IntegrableOn (fun s => Gx (s,y)) (Icc a b) volume)
    (hfx : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      (∫ r in s..t, Gx (r,y)) = f (t,y)-f (s,y))
    (hfy : ∀ᵐ s ∂volume.restrict (Icc a b), ∀ t ∈ Icc c d, ∀ w ∈ Icc c d,
      (∫ r in t..w, Gy (s,r)) = f (s,w)-f (s,t))
    (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) :
    |f (x,y) - (⨍ s in Icc a b, ⨍ t in Icc c d, f (s,t))| ≤
      (∫ s in Icc a b, |Gx (s,y)|) +
        (⨍ s in Icc a b, ∫ t in Icc c d, |Gy (s,t)|) := by
  let : NeZero ((volume : Measure ℝ).restrict (Icc a b)) :=
    ⟨volume_restrict_Icc_ne_zero hab⟩
  let : NeZero ((volume : Measure ℝ).restrict (Icc c d)) :=
    ⟨volume_restrict_Icc_ne_zero hcd⟩
  have hm : Integrable (fun s => ⨍ t in Icc c d, f (s,t))
      (volume.restrict (Icc a b)) := by
    simp only [average_eq, smul_eq_mul]
    exact hf.integral_prod_left.const_mul _
  apply abs_sub_iterated_average_le hf.prod_right_ae hm hGy.abs.integral_prod_left
  filter_upwards [hGy.prod_right_ae, hfy, ae_restrict_mem measurableSet_Icc]
    with s hs hfs hsmem
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  calc
    |f (x,y)-f (s,t)| ≤ |f (x,y)-f (s,y)| + |f (s,y)-f (s,t)| := abs_sub_le _ _ _
    _ ≤ (∫ r in Icc a b, |Gx (r,y)|) + (∫ r in Icc c d, |Gy (s,r)|) :=
      add_le_add (interval_increment_le_integral (u := fun r => f (r,y)) hrow hx hsmem (hfx x hx s hsmem))
        (interval_increment_le_integral (u := fun r => f (s,r)) hs hy ht (hfs y hy t ht))

lemma rectangle_ae_mean_bound {f Gx Gy : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hab : a < b) (hcd : c < d)
    (hf : Integrable f ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hGx : Integrable Gx ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hGy : Integrable Gy ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hfx : ∀ᵐ t ∂volume.restrict (Icc c d), ∀ s ∈ Icc a b, ∀ w ∈ Icc a b,
      (∫ r in s..w, Gx (r,t)) = f (w,t)-f (s,t))
    (hfy : ∀ᵐ s ∂volume.restrict (Icc a b), ∀ t ∈ Icc c d, ∀ w ∈ Icc c d,
      (∫ r in t..w, Gy (s,r)) = f (s,w)-f (s,t)) :
    ∀ᵐ y ∂volume.restrict (Icc c d), ∀ x ∈ Icc a b,
    |f (x,y) - (⨍ s in Icc a b, ⨍ t in Icc c d, f (s,t))| ≤
      (∫ s in Icc a b, |Gx (s,y)|) +
        (⨍ s in Icc a b, ∫ t in Icc c d, |Gy (s,t)|) := by
  filter_upwards [hGx.prod_left_ae, hfx, ae_restrict_mem measurableSet_Icc]
    with y hy hfy' hymem
  intro x hx
  exact rectangle_point_mean_bound hab hcd hf hGy hy hfy' hfy hx hymem

end CircleDomainRigidity

end

end OAI
