import OAI.Analysis.CircleDomains.Modulus.OpenGapPayment
import OAI.Analysis.CircleDomains.Selection.FiniteLineGaps

namespace OAI

/-!
# Line payment for an actual finite family of closed intervals

The removed intervals are ordered and disjoint. Smoothness is required
only on their complement. Endpoint cluster bounds pay for the jumps;
absolute continuity of the individual domain intervals is derived.
-/

open Set Function Filter MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

theorem line_payment_of_ordered_holes
    {n : ℕ} {a b : ℝ} (hab : a < b) (H : Fin n → ℝ × ℝ)
    (hinside : ∀ i, a < (H i).1 ∧ (H i).1 ≤ (H i).2 ∧ (H i).2 < b)
    (hsep : ∀ i j, i < j → (H i).2 < (H j).1)
    {f d ρ : ℝ → ℝ} (A : Fin n → ℝ)
    (hd : ∀ x ∈ Icc a b ∩ (⋃ i, Icc (H i).1 (H i).2)ᶜ, HasDerivAt f (d x) x)
    (hcd : ContinuousOn d (Icc a b ∩ (⋃ i, Icc (H i).1 (H i).2)ᶜ))
    (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x)
    (hdom : ∀ x ∈ Icc a b ∩ (⋃ i, Icc (H i).1 (H i).2)ᶜ, |d x| ≤ ρ x)
    (ha : ContinuousAt f a) (hb : ContinuousAt f b) (hzero : f a = 0) (hone : f b = 1)
    (hjump : ∀ i u v,
      MapClusterPt u (𝓝[Icc a b ∩ (⋃ j, Icc (H j).1 (H j).2)ᶜ] (H i).1) f →
      MapClusterPt v (𝓝[Icc a b ∩ (⋃ j, Icc (H j).1 (H j).2)ᶜ] (H i).2) f → |v - u| ≤ A i) :
    1 ≤ (∫ x, ρ x) + ∑ i, A i := by
  let gap := gapsAfterHoles a b H
  let D := Icc a b ∩ (⋃ i, Icc (H i).1 (H i).2)ᶜ
  have hfirst : Monotone (fun i => (H i).1) := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hij
    · rfl
    · exact (hinside i).2.1.trans (hsep i j hij).le
  have hlast : Monotone (fun i => (H i).2) := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hij
    · rfl
    · exact (hsep i j hij).le.trans (hinside j).2.1
  have hgap (i : Fin (n + 1)) : (gap i).1 < (gap i).2 :=
    gapsAfterHoles_strict hab H hinside hsep i
  have hgapAB (i : Fin (n + 1)) : Ioo (gap i).1 (gap i).2 ⊆ Icc a b := by
    have hleft : a ≤ (gap i).1 := by
      change a ≤ (gapsAfterHoles a b H i).1
      refine Fin.cases ?_ (fun j => ?_) i
      · exact le_rfl
      · exact (hinside j).1.le.trans (hinside j).2.1
    have hright : (gap i).2 ≤ b := by
      change (gapsAfterHoles a b H i).2 ≤ b
      refine Fin.lastCases (motive := fun j : Fin (n + 1) =>
        (gapsAfterHoles a b H j).2 ≤ b) ?_ (fun j => ?_) i
      · simp only [gapsAfterHoles_last_snd, le_refl]
      · simpa only [gapsAfterHoles_castSucc_snd] using (hinside j).2.1.trans (hinside j).2.2.le
    exact fun _ hx => ⟨hleft.trans hx.1.le, hx.2.le.trans hright⟩
  have hgapD (i : Fin (n + 1)) : Ioo (gap i).1 (gap i).2 ⊆ D := by
    intro x hx
    refine ⟨hgapAB i hx, ?_⟩
    exact fun h => by
      obtain ⟨j, hj⟩ := mem_iUnion.mp h
      exact gapsAfterHoles_avoid a b H hfirst hlast i hx j hj
  have hgi (i : Fin (n + 1)) : IntervalIntegrable d volume (gap i).1 (gap i).2 := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (hgap i).le).mpr
    apply hρ.integrableOn.mono' ((hcd.mono (hgapD i)).aestronglyMeasurable measurableSet_Ioo)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa only [Real.norm_eq_abs] using hdom x (hgapD i hx)
  apply line_payment_from_open_gaps n (fun i => (gap i).1) (fun i => (gap i).2)
    f d ρ A hgap (fun i x hx => hd x (hgapD i hx)) hgi hρ hpos
    (fun i x hx => hdom x (hgapD i hx))
    (gapsAfterHoles_disjoint a b H (fun i => (hinside i).2.1) hfirst)
  · simpa only [gap, gapsAfterHoles_zero_fst, ← hzero] using
      ha.mono_left nhdsWithin_le_nhds
  · simpa only [gap, gapsAfterHoles_last_snd, ← hone] using
      hb.mono_left nhdsWithin_le_nhds
  · intro i u v hu hv
    have hnleft : NeBot (𝓝[Ioo (gap i.castSucc).1 (gap i.castSucc).2] (gap i.castSucc).2) :=
      mem_closure_iff_nhdsWithin_neBot.mp (by
        rw [closure_Ioo (hgap i.castSucc).ne]
        exact right_mem_Icc.mpr (hgap i.castSucc).le)
    have hnright : NeBot (𝓝[Ioo (gap i.succ).1 (gap i.succ).2] (gap i.succ).1) :=
      mem_closure_iff_nhdsWithin_neBot.mp (by
        rw [closure_Ioo (hgap i.succ).ne]
        exact left_mem_Icc.mpr (hgap i.succ).le)
    have hlu := hu.mapClusterPt.mono (nhdsWithin_mono _ (hgapD i.castSucc))
    have hlv := hv.mapClusterPt.mono (nhdsWithin_mono _ (hgapD i.succ))
    apply hjump i u v
    · simpa only [gap, gapsAfterHoles_castSucc_snd] using hlu
    · simpa only [gap, gapsAfterHoles_succ_fst] using hlv

end CircleDomainRigidity

end OAI
