import OAI.MathematicalPhysics.Transonic.Core

namespace OAI

section

namespace SepticProfile.RegularContinuation
open Set

theorem clamped_no_return {a b c d : ℝ} (hcd : c≤d)
    {f : ℝ×ℝ → ℝ} {u : ℝ → ℝ}
    (hud : ∀ t ∈ Icc a b, HasDerivWithinAt u (f (t,clamp c d (u t))) (Icc a b) t)
    (hlo : ∀ t ∈ Icc a b, f (t,c)<0)
    (hhi : ∀ t ∈ Icc a b, 0<f (t,d))
    (hend : u b ∈ Ioo c d) :
    (∀ t ∈ Icc a b, u t ∈ Ioo c d) ∧
    ∀ t ∈ Icc a b, HasDerivWithinAt u (f (t,u t)) (Icc a b) t := by
  have hc : ContinuousOn u (Icc a b) := fun t ht => (hud t ht).continuousWithinAt
  have hrange (t:ℝ) (ht:t ∈ Icc a b) : u t ∈ Ioo c d := by
    have hsub : Icc t b ⊆ Icc a b := Icc_subset_Icc_left ht.1
    have hd (s:ℝ) (hs:s ∈ Ico t b) :
        HasDerivWithinAt u (f (s,clamp c d (u s))) (Ici s) s := by
      apply (hud s (hsub ⟨hs.1,hs.2.le⟩)).mono_of_mem_nhdsWithin
      exact Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left (ht.1.trans hs.1))
    constructor
    · by_contra hlt
      have hstart : u t≤c := le_of_not_gt hlt
      have hh := image_le_of_deriv_right_lt_deriv_boundary' (hc.mono hsub) hd
        (B:=fun _ => c) (B':=fun _ => 0) hstart continuousOn_const
        (fun s _ => (hasDerivAt_const s c).hasDerivWithinAt)
      have hh' : ∀ s ∈ Icc t b, u s≤c := by
        apply hh
        intro s hs he
        rw [he,clamp_eq (show c ∈ Icc c d from ⟨le_rfl,hcd⟩)]
        exact hlo s (hsub ⟨hs.1,hs.2.le⟩)
      have := hh' b ⟨ht.2,le_rfl⟩
      linarith [hend.1]
    · by_contra hlt
      have hstart : -u t≤ -d := by linarith [le_of_not_gt hlt]
      have hh := image_le_of_deriv_right_lt_deriv_boundary' (hc.mono hsub).neg
        (fun s hs => (hd s hs).neg) (B:=fun _ => -d) (B':=fun _ => 0)
        hstart continuousOn_const (fun s _ => (hasDerivAt_const s (-d)).hasDerivWithinAt)
      have hh' : ∀ s ∈ Icc t b, -u s≤ -d := by
        apply hh
        intro s hs he
        have he' : u s=d := neg_inj.mp he
        rw [he',clamp_eq (show d ∈ Icc c d from ⟨hcd,le_rfl⟩)]
        exact neg_neg_of_pos (hhi s (hsub ⟨hs.1,hs.2.le⟩))
      have := hh' b ⟨ht.2,le_rfl⟩
      linarith [hend.2]
  refine ⟨hrange,?_⟩
  intro t ht
  simpa only [clamp_eq ⟨(hrange t ht).1.le,(hrange t ht).2.le⟩] using hud t ht

end SepticProfile.RegularContinuation


end

end OAI
