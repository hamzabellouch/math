import Mathlib

namespace OAI

/-! # Integrating an inverse-square-root derivative bound at time zero -/

open Set

namespace RegularPointCoordinates

/-- Integrating a heat-smoothing singularity together with a bounded error. -/
theorem abs_sub_le_of_sqrt_derivative_bound_add {F D : ℝ → ℝ} {A B T : ℝ}
    (hT : 0 < T) (hc : ContinuousOn F (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt F (D t) t)
    (hb : ∀ t ∈ Ioo 0 T, |D t| ≤ A / Real.sqrt t+B) :
    |F T - F 0| ≤ 2*A*Real.sqrt T+B*T := by
  have hs : ContinuousOn (fun t : ℝ => 2*A*Real.sqrt t+B*t) (Icc 0 T) := by fun_prop
  have hs' (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivAt (fun t : ℝ => 2*A*Real.sqrt t+B*t) (A / Real.sqrt t+B) t := by
    have hh : HasDerivAt (fun t : ℝ => 2*A*Real.sqrt t) (A/Real.sqrt t) t := by
      convert (Real.hasDerivAt_sqrt ht.1.ne').const_mul (2*A) using 1
      field_simp
    simpa only [Pi.add_apply,id_eq,mul_one] using! hh.add ((hasDerivAt_id t).const_mul B)
  have hp := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0:ℝ) T)
    (hc.add hs) (f' := fun t => D t+(A/Real.sqrt t+B))
    (fun t ht => ((hd t (by simpa only [interior_Icc,mem_Ioo] using ht)).add
      (hs' t (by simpa only [interior_Icc,mem_Ioo] using ht))).hasDerivWithinAt)
    (fun t ht => by
      have ht' : t ∈ Ioo 0 T := by simpa only [interior_Icc] using ht
      linarith [(abs_le.mp (hb t ht')).1])
  have hm := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0:ℝ) T)
    (hc.sub hs) (f' := fun t => D t-(A/Real.sqrt t+B))
    (fun t ht => ((hd t (by simpa only [interior_Icc,mem_Ioo] using ht)).sub
      (hs' t (by simpa only [interior_Icc,mem_Ioo] using ht))).hasDerivWithinAt)
    (fun t ht => by
      have ht' : t ∈ Ioo 0 T := by simpa only [interior_Icc] using ht
      linarith [(abs_le.mp (hb t ht')).2])
  have hp' := hp (show (0:ℝ) ∈ Icc 0 T from ⟨le_rfl,hT.le⟩)
    (show T ∈ Icc 0 T from ⟨hT.le,le_rfl⟩) hT.le
  have hm' := hm (show (0:ℝ) ∈ Icc 0 T from ⟨le_rfl,hT.le⟩)
    (show T ∈ Icc 0 T from ⟨hT.le,le_rfl⟩) hT.le
  simp only [Pi.add_apply,Pi.sub_apply,Real.sqrt_zero,mul_zero,add_zero,sub_zero] at hp' hm'
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- The integrable singularity of heat smoothing costs exactly a square root
of elapsed time. Only continuity is needed at the initial time. -/
theorem abs_sub_le_of_sqrt_derivative_bound {F D : ℝ → ℝ} {A T : ℝ}
    (hT : 0 < T) (hc : ContinuousOn F (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt F (D t) t)
    (hb : ∀ t ∈ Ioo 0 T, |D t| ≤ A / Real.sqrt t) :
    |F T - F 0| ≤ 2*A*Real.sqrt T := by
  simpa only [zero_mul,add_zero] using
    abs_sub_le_of_sqrt_derivative_bound_add (B := 0) hT hc hd
      (fun t ht => by simpa only [add_zero] using hb t ht)

end RegularPointCoordinates

end OAI
