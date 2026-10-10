import OAI.MathematicalPhysics.Transonic.Shooting.ClampedFamily

namespace OAI

section

namespace SepticProfile.RegularContinuation
open Set
theorem clamped_stays_between_strict {a b c d : ℝ} {u : ℝ → ℝ}
    {f : ℝ×ℝ → ℝ}
    (huc : ContinuousOn u (Icc a b))
    (hud : ∀ t ∈ Icc a b, HasDerivWithinAt u (f (t,clamp c d (u t))) (Icc a b) t)
    (lo hi dlo dhi : ℝ → ℝ)
    (hloder : ∀ t ∈ Icc a b, HasDerivAt lo (dlo t) t)
    (hhider : ∀ t ∈ Icc a b, HasDerivAt hi (dhi t) t)
    (hlorange : ∀ t ∈ Icc a b, lo t ∈ Icc c d)
    (hhirange : ∀ t ∈ Icc a b, hi t ∈ Icc c d)
    (hlostrict : ∀ t ∈ Icc a b, dlo t<f (t,lo t))
    (hhistrict : ∀ t ∈ Icc a b, f (t,hi t)<dhi t)
    (hu0 : u a ∈ Icc (lo a) (hi a)) :
    (∀ t ∈ Icc a b, u t ∈ Icc (lo t) (hi t)) ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt u (f (t,u t)) (Icc a b) t := by
  have hright (t : ℝ) (ht : t ∈ Ico a b) : HasDerivWithinAt u
      (f (t,clamp c d (u t))) (Ici t) t := by
    apply (hud t ⟨ht.1,le_of_lt ht.2⟩).mono_of_mem_nhdsWithin
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)
  have hupper : ∀ t ∈ Icc a b, u t≤hi t := by
    apply image_le_of_deriv_right_lt_deriv_boundary' huc hright
      (B' := dhi) hu0.2
      (fun t ht => (hhider t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hhider t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt)
    intro t ht he
    rw [he,clamp_eq (hhirange t ⟨ht.1,ht.2.le⟩)]
    exact hhistrict t ⟨ht.1,ht.2.le⟩
  have hlower : ∀ t ∈ Icc a b, lo t≤u t := by
    have hh := image_le_of_deriv_right_lt_deriv_boundary' huc.neg
      (fun t ht => (hright t ht).neg) (B := fun t => -lo t) (B' := fun t => -dlo t)
      (by change -u a ≤ -lo a; linarith [hu0.1])
      (fun t ht => (hloder t ht).neg.continuousAt.continuousWithinAt)
      (fun t ht => (hloder t ⟨ht.1,ht.2.le⟩).neg.hasDerivWithinAt)
    have hh' : ∀ t ∈ Icc a b, -u t≤ -lo t := by
      apply hh
      intro t ht he
      have he' : u t=lo t := neg_inj.mp he
      rw [he',clamp_eq (hlorange t ⟨ht.1,ht.2.le⟩)]
      exact neg_lt_neg (hlostrict t ⟨ht.1,ht.2.le⟩)
    intro t ht
    linarith [hh' t ht]
  refine ⟨fun t ht => ⟨hlower t ht,hupper t ht⟩,?_⟩
  intro t ht
  have htu : u t ∈ Icc c d :=
    ⟨le_trans (hlorange t ht).1 (hlower t ht),le_trans (hupper t ht) (hhirange t ht).2⟩
  simpa only [clamp_eq htu] using hud t ht

end SepticProfile.RegularContinuation


end

end OAI
