import OAI.MathematicalPhysics.Transonic.Profile.PhysicalExterior

namespace OAI

section

namespace SepticProfile.RegularContinuation
open Set

theorem clamped_unique {a b c d : ℝ} (hcd : c≤d)
    {f : ℝ×ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Icc a b ×ˢ Icc c d))
    {u v : ℝ → ℝ} (hu : ∀ t ∈ Icc a b,
      HasDerivWithinAt u (f (t,clamp c d (u t))) (Icc a b) t)
    (hv : ∀ t ∈ Icc a b,
      HasDerivWithinAt v (f (t,clamp c d (v t))) (Icc a b) t)
    (hinit : u a=v a) : EqOn u v (Icc a b) := by
  obtain ⟨K,hK⟩ := hf.exists_lipschitzOnWith (by norm_num)
    ((convex_Icc a b).prod (convex_Icc c d)) (isCompact_Icc.prod isCompact_Icc)
  have hLip (t:ℝ) (ht:t ∈ Icc a b) (x y:ℝ) :
      ‖f (t,clamp c d x)-f (t,clamp c d y)‖≤K*‖x-y‖ := by
    have hb1 := hK.norm_sub_le (show (t,clamp c d x) ∈ Icc a b ×ˢ Icc c d from ⟨ht,clamp_mem hcd x⟩)
      (show (t,clamp c d y) ∈ Icc a b ×ˢ Icc c d from ⟨ht,clamp_mem hcd y⟩)
    have hb2 := (clamp_lipschitz c d).norm_sub_le x y
    simp only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero,
      max_eq_right (norm_nonneg _),NNReal.coe_one,one_mul] at hb1 hb2
    exact hb1.trans (mul_le_mul_of_nonneg_left hb2 K.coe_nonneg)
  have hdu (t:ℝ) (ht:t ∈ Ico a b) :
      HasDerivWithinAt u (f (t,clamp c d (u t))) (Ici t) t := by
    apply (hu t ⟨ht.1,ht.2.le⟩).mono_of_mem_nhdsWithin
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)
  have hdv (t:ℝ) (ht:t ∈ Ico a b) :
      HasDerivWithinAt v (f (t,clamp c d (v t))) (Ici t) t := by
    apply (hv t ⟨ht.1,ht.2.le⟩).mono_of_mem_nhdsWithin
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    ((show ContinuousOn u (Icc a b) from fun t ht => (hu t ht).continuousWithinAt).sub
      (show ContinuousOn v (Icc a b) from fun t ht => (hv t ht).continuousWithinAt))
    (fun t ht => (hdu t ht).sub (hdv t ht)) (sub_eq_zero.mpr hinit)
    (fun t ht => hLip t ⟨ht.1,ht.2.le⟩ (u t) (v t))
  exact fun t ht => sub_eq_zero.mp (hzero t ht)

end SepticProfile.RegularContinuation

end

end OAI
