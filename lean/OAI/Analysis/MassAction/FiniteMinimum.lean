import Mathlib

namespace OAI

universe uIota

noncomputable section

open Set Filter
open scoped Topology

namespace Problem326

/-- A finite minimum has nonnegative lower right slope when every active
branch has a nonnegative right derivative. Inactive branches need only be
right-continuous. -/
theorem eventually_slope_finset_inf'_gt
    {ι : Type uIota} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → ℝ → ℝ} {x : ℝ}
    (hc : ∀ i ∈ s, ContinuousWithinAt (f i) (Ioi x) x)
    (hd : ∀ i ∈ s, f i x = s.inf' hs (fun j => f j x) →
      ∃ v : ℝ, 0 ≤ v ∧ HasDerivWithinAt (f i) v (Ici x) x)
    {r : ℝ} (hr : r < 0) :
    ∀ᶠ y in 𝓝[>] x,
      r < slope (fun t => s.inf' hs (fun i => f i t)) x y := by
  have hi : ∀ i ∈ s, ∀ᶠ y in 𝓝[>] x,
      s.inf' hs (fun j => f j x) + r * (y - x) < f i y := by
    intro i his
    have hle : s.inf' hs (fun j => f j x) ≤ f i x :=
      Finset.inf'_le _ his
    rcases hle.eq_or_lt with heq | hlt
    · obtain ⟨v, hv, hvd⟩ := hd i his heq.symm
      have hslope : ∀ᶠ y in 𝓝[>] x, r < slope (f i) x y :=
        (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl x)).1
          hvd.Ioi_of_Ici (Ioi_mem_nhds (lt_of_lt_of_le hr hv))
      filter_upwards [hslope, eventually_mem_nhdsWithin] with y hy hxy
      rw [slope_def_field] at hy
      have hm := (lt_div_iff₀ (sub_pos.mpr hxy)).mp hy
      rw [heq]
      linarith
    · have hc' : ∀ᶠ y in 𝓝[>] x, s.inf' hs (fun j => f j x) < f i y :=
        hc i his (Ioi_mem_nhds hlt)
      filter_upwards [hc', eventually_mem_nhdsWithin] with y hy hxy
      have hm : r * (y - x) < 0 := mul_neg_of_neg_of_pos hr (sub_pos.mpr hxy)
      linarith
  have hall := (s.eventually_all).mpr hi
  filter_upwards [hall, eventually_mem_nhdsWithin] with y hy hxy
  have hm : s.inf' hs (fun j => f j x) + r * (y - x) <
      s.inf' hs (fun i => f i y) := (Finset.lt_inf'_iff hs).mpr hy
  rw [slope_def_field]
  apply (lt_div_iff₀ (sub_pos.mpr hxy)).mpr
  linarith

/-- Endpoint comparison for a finite minimum, using only derivatives of active
branches. The right derivative is required at the left endpoint. -/
theorem finset_inf'_initial_le
    {ι : Type uIota} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → ℝ → ℝ} {a b : ℝ}
    (hc : ∀ i ∈ s, ContinuousOn (f i) (Icc a b))
    (hd : ∀ x ∈ Ico a b, ∀ i ∈ s,
      f i x = s.inf' hs (fun j => f j x) →
      ∃ v : ℝ, 0 ≤ v ∧ HasDerivWithinAt (f i) v (Ici x) x) :
    ∀ t ∈ Icc a b, s.inf' hs (fun i => f i a) ≤ s.inf' hs (fun i => f i t) := by
  let F : ℝ → ℝ := fun t => s.inf' hs (fun i => f i t)
  have hFc : ContinuousOn F (Icc a b) := ContinuousOn.finset_inf'_apply hs hc
  have hfence : ∀ t ∈ Icc a b, -F t ≤ -F a := by
    apply image_le_of_liminf_slope_right_le_deriv_boundary hFc.neg (le_refl (-F a))
      continuousOn_const (B' := fun _ => 0)
    · intro x hx
      exact (hasDerivAt_const x (-F a)).hasDerivWithinAt
    · intro x hx r hr
      have hlocal := eventually_slope_finset_inf'_gt hs
        (fun i hi => (hc i hi x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGT_of_mem hx))
        (hd x hx) (neg_neg_of_pos hr)
      apply Filter.Eventually.frequently
      filter_upwards [hlocal] with y hy
      change slope (fun t => -F t) x y < r
      rw [slope_neg]
      change -r < slope F x y at hy
      linarith
  intro t ht
  exact neg_le_neg_iff.mp (hfence t ht)

/-- A finite minimum is monotone when every active branch has nonnegative
right derivative. No derivative is required of an inactive branch. -/
theorem monotoneOn_finset_inf'_of_active_right_deriv_nonneg
    {ι : Type uIota} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → ℝ → ℝ} {a b : ℝ}
    (hc : ∀ i ∈ s, ContinuousOn (f i) (Icc a b))
    (hd : ∀ x ∈ Ico a b, ∀ i ∈ s,
      f i x = s.inf' hs (fun j => f j x) →
      ∃ v : ℝ, 0 ≤ v ∧ HasDerivWithinAt (f i) v (Ici x) x) :
    MonotoneOn (fun t => s.inf' hs (fun i => f i t)) (Icc a b) := by
  intro u hu v hv huv
  apply finset_inf'_initial_le hs
    (fun i hi => (hc i hi).mono (Icc_subset_Icc hu.1 hv.2))
    (fun x hx => hd x ⟨hu.1.trans hx.1, hx.2.trans_le hv.2⟩)
    v ⟨huv, le_refl v⟩

/-- Interior-derivative form: continuity handles both endpoints, so this applies
to solution curves whose ODE is only assumed on an open interval. -/
theorem monotoneOn_finset_inf'_of_active_deriv_nonneg
    {ι : Type uIota} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → ℝ → ℝ} {a b : ℝ}
    (hc : ∀ i ∈ s, ContinuousOn (f i) (Icc a b))
    (hd : ∀ x ∈ Ioo a b, ∀ i ∈ s,
      f i x = s.inf' hs (fun j => f j x) →
      ∃ v : ℝ, 0 ≤ v ∧ HasDerivAt (f i) v x) :
    MonotoneOn (fun t => s.inf' hs (fun i => f i t)) (Icc a b) := by
  intro u hu v hv huv
  rcases huv.eq_or_lt with rfl | huv
  · exact le_refl _
  let F : ℝ → ℝ := fun t => s.inf' hs (fun i => f i t)
  have hFc : ContinuousOn F (Icc a b) := ContinuousOn.finset_inf'_apply hs hc
  have hclosure : u ∈ closure (Ioo u v) := by
    rw [closure_Ioo huv.ne]
    exact ⟨le_refl u, huv.le⟩
  have hsub : Ioo u v ⊆ Icc a b := by
    intro y hy
    exact ⟨hu.1.trans hy.1.le, hy.2.le.trans hv.2⟩
  apply ContinuousWithinAt.closure_le hclosure
    ((hFc u hu).mono hsub) continuousWithinAt_const
  intro y hy
  apply finset_inf'_initial_le hs
    (fun i hi => (hc i hi).mono (Icc_subset_Icc (hu.1.trans hy.1.le) hv.2))
    ?_ v ⟨hy.2.le, le_refl v⟩
  intro x hx i hi hactive
  obtain ⟨w, hw, hwd⟩ := hd x
    ⟨lt_of_le_of_lt hu.1 (hy.1.trans_le hx.1), hx.2.trans_le hv.2⟩ i hi hactive
  exact ⟨w, hw, hwd.hasDerivWithinAt⟩

end Problem326

end

end OAI
