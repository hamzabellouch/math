import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv

namespace OAI

/-! # Extending the interior derivative estimate to closed time slabs -/

open Set

namespace DefocusingNLS

theorem norm_sub_le_of_interior_derivative
    (F D : ℝ → ℂ) (T C : ℝ) (hT : 0 ≤ T) (hF : Continuous F)
    (hd : ∀ s ∈ Ioo 0 T, HasDerivAt F (D s) s)
    (hbound : ∀ s ∈ Ioo 0 T, ‖D s‖ ≤ C)
    (s t : ℝ) (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    ‖F t - F s‖ ≤ C * |t - s| := by
  rcases hT.eq_or_lt with hT | hT
  · have hs0 : s = 0 := by linarith [hs.1, hs.2]
    have ht0 : t = 0 := by linarith [ht.1, ht.2]
    simp [hs0, ht0]
  have hclosed : IsClosed {p : ℝ × ℝ | ‖F p.2 - F p.1‖ ≤ C * |p.2 - p.1|} :=
    isClosed_le ((hF.comp continuous_snd).sub (hF.comp continuous_fst)).norm
      (continuous_const.mul ((continuous_snd.sub continuous_fst).abs))
  have hin : Ioo (0 : ℝ) T ×ˢ Ioo (0 : ℝ) T ⊆
      {p : ℝ × ℝ | ‖F p.2 - F p.1‖ ≤ C * |p.2 - p.1|} := by
    intro p hp
    have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hd x hx).hasDerivWithinAt) hbound (convex_Ioo (0 : ℝ) T) hp.1 hp.2
    simpa only [Set.mem_ofPred_eq, Real.norm_eq_abs] using he
  have he := hclosed.closure_subset_iff.mpr hin
  have hmem : (s, t) ∈ closure (Ioo (0 : ℝ) T ×ˢ Ioo (0 : ℝ) T) := by
    rw [closure_prod_eq, closure_Ioo hT.ne]
    exact ⟨hs, ht⟩
  exact he hmem

end DefocusingNLS

end OAI
