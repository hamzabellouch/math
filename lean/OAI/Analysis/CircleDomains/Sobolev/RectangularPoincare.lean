import OAI.Analysis.CircleDomains.Modulus.RectangleMeanOscillation

namespace OAI

/-! Rectangular Poincare with explicit side lengths and area averages. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma rectangular_poincare {f Gx Gy : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hab : a < b) (hcd : c < d)
    (hf : Integrable f ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hGx : Integrable Gx ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hGy : Integrable Gy ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hfx : ∀ᵐ t ∂volume.restrict (Icc c d), ∀ s ∈ Icc a b, ∀ w ∈ Icc a b,
      (∫ r in s..w, Gx (r,t)) = f (w,t)-f (s,t))
    (hfy : ∀ᵐ s ∂volume.restrict (Icc a b), ∀ t ∈ Icc c d, ∀ w ∈ Icc c d,
      (∫ r in t..w, Gy (s,r)) = f (s,w)-f (s,t)) :
    (⨍ p, |f p-(⨍ q, f q ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)))|
      ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) ≤
    (b-a)*(⨍ p, |Gx p| ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) +
    (d-c)*(⨍ p, |Gy p| ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
  let m := ⨍ s in Icc a b, ⨍ t in Icc c d, f (s,t)
  have ho : Integrable (fun p => |f p-m|)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) :=
    (hf.sub (integrable_const m)).abs
  calc
    _ = ⨍ y in Icc c d, ⨍ x in Icc a b, |f (x,y)-m| := by
      rw [product_average hf]
      exact (product_average ho).trans (iterated_average_swap ho)
    _ ≤ (⨍ y in Icc c d, ∫ x in Icc a b, |Gx (x,y)|) +
        (⨍ x in Icc a b, ∫ y in Icc c d, |Gy (x,y)|) :=
      rectangle_mean_oscillation hab hcd hf hGx hGy hfx hfy
    _ = _ := by
      rw [average_integral_first hGx.abs, average_integral_second hGy.abs]
      simp only [measureReal_restrict_apply_univ, Real.volume_real_Icc_of_le hab.le,
        Real.volume_real_Icc_of_le hcd.le]

end CircleDomainRigidity

end

end OAI
