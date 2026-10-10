import OAI.Analysis.CircleDomains.Sobolev.SmoothOpenImageMeasure

namespace OAI

/-! Including the two endpoints of a slice does not increase its image
measure. This gives the derivative bound on a closed component segment. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem smooth_closed_slice_image_measure_le {V : Set ℝ} (hV : IsOpen V)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f V) {a b : ℝ}
    (hi : IntegrableOn (fun x => |deriv f x|) (Icc a b ∩ V) volume) :
    volume (f '' (Icc a b ∩ V)) ≤
      ENNReal.ofReal (∫ x in Icc a b ∩ V, |deriv f x|) := by
  let U := Ioo a b ∩ V
  have hU : IsOpen U := isOpen_Ioo.inter hV
  have hUV : U ⊆ Icc a b ∩ V := inter_subset_inter Ioo_subset_Icc_self Subset.rfl
  have hsub : f '' (Icc a b ∩ V) ⊆ f '' U ∪ {f a, f b} := by
    rintro _ ⟨x,hx,rfl⟩
    by_cases ha : x = a
    · subst x; exact Or.inr (by simp)
    by_cases hb : x = b
    · subst x; exact Or.inr (by simp)
    exact Or.inl ⟨x,⟨⟨lt_of_le_of_ne hx.1.1 (Ne.symm ha),
      lt_of_le_of_ne hx.1.2 hb⟩,hx.2⟩,rfl⟩
  have hnull : volume ({f a, f b} : Set ℝ) = 0 := ((finite_singleton (f b)).insert (f a)).measure_zero volume
  calc
    _ ≤ volume (f '' U ∪ {f a,f b}) := measure_mono hsub
    _ ≤ volume (f '' U) + volume ({f a,f b} : Set ℝ) := measure_union_le _ _
    _ = volume (f '' U) := by rw [hnull,add_zero]
    _ ≤ ENNReal.ofReal (∫ x in U, |deriv f x|) :=
      smooth_open_image_measure_le hU (hf.mono inter_subset_right) (hi.mono_set hUV)
    _ ≤ _ := ENNReal.ofReal_le_ofReal (setIntegral_mono_set hi
      (Eventually.of_forall (fun _ => abs_nonneg _)) hUV.eventuallySubset)

end CircleDomainRigidity

end

end OAI
