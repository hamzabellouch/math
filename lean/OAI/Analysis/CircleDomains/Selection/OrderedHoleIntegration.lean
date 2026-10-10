import OAI.Analysis.CircleDomains.Transfer.FilledGapIntegration
import OAI.Analysis.CircleDomains.Selection.FiniteGapGeometry

namespace OAI

/-! Integration by parts for a bounded filling of actual ordered closed
intervals. Finite variation constructs every endpoint trace used below. -/
open Set Function Filter MeasureTheory
open scoped Topology
namespace CircleDomainRigidity

 theorem filled_integration_of_ordered_holes
    {n : ℕ} {a b : ℝ} (hab : a < b) (H : Fin n → ℝ × ℝ)
    (hinside : ∀ i, a < (H i).1 ∧ (H i).1 ≤ (H i).2 ∧ (H i).2 < b)
    (hsep : ∀ i j, i < j → (H i).2 < (H j).1)
    {f d F ρ : ℝ → ℝ} (value A : Fin n → ℝ)
    (hd : ∀ x ∈ Icc a b ∩ (⋃ i, Icc (H i).1 (H i).2)ᶜ, HasDerivAt f (d x) x)
    (hcd : ContinuousOn d (Icc a b ∩ (⋃ i, Icc (H i).1 (H i).2)ᶜ))
    (hρ : Integrable ρ)
    (hdom : ∀ x ∈ Icc a b ∩ (⋃ i, Icc (H i).1 (H i).2)ᶜ, |d x| ≤ ρ x)
    (hF : EqOn F (clipScalar ∘ f) (Icc a b ∩ (⋃ i, Icc (H i).1 (H i).2)ᶜ))
    (hfill : ∀ i, EqOn F (fun _ => clipScalar (value i)) (Icc (H i).1 (H i).2))
    (hcluster : ∀ i p u, p ∈ Icc (H i).1 (H i).2 →
      MapClusterPt u (𝓝[Icc a b ∩ (⋃ j, Icc (H j).1 (H j).2)ᶜ] p) f →
        |u - value i| ≤ A i)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hzero : φ a = 0) (hone : φ b = 0)
    (hint : Integrable (fun x => F x * deriv φ x))
    (hdint : Integrable (fun x => deriv F x * φ x))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, |φ x| ≤ C) (hA : ∀ i, 0 ≤ A i) :
    |(∫ x in a..b, F x * deriv φ x) + (∫ x in a..b, deriv F x * φ x)| ≤
      2 * C * ∑ i, A i := by
  let gap := gapsAfterHoles a b H
  let D := Icc a b ∩ (⋃ i, Icc (H i).1 (H i).2)ᶜ
  have hgap (i : Fin (n + 1)) : (gap i).1 < (gap i).2 :=
    gapsAfterHoles_strict hab H hinside hsep i
  have hgapD (i : Fin (n + 1)) : Ioo (gap i).1 (gap i).2 ⊆ D :=
    gapsAfterHoles_subset_residual H hinside hsep i
  have hgi (i : Fin (n + 1)) : IntervalIntegrable d volume (gap i).1 (gap i).2 := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (hgap i).le).mpr
    apply hρ.integrableOn.mono' ((hcd.mono (hgapD i)).aestronglyMeasurable measurableSet_Ioo)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa only [Real.norm_eq_abs] using hdom x (hgapD i hx)
  have hleft (i : Fin n) (u : ℝ)
      (hu : Tendsto f (𝓝[Ioo (gap i.castSucc).1 (gap i.castSucc).2]
        (gap i.castSucc).2) (𝓝 u)) : |u - value i| ≤ A i := by
    have : NeBot (𝓝[Ioo (gap i.castSucc).1 (gap i.castSucc).2] (gap i.castSucc).2) :=
      mem_closure_iff_nhdsWithin_neBot.mp (by
        rw [closure_Ioo (hgap i.castSucc).ne]
        exact right_mem_Icc.mpr (hgap i.castSucc).le)
    apply hcluster i (H i).1 u (left_mem_Icc.mpr (hinside i).2.1)
    simpa only [gap, gapsAfterHoles_castSucc_snd] using
      hu.mapClusterPt.mono (nhdsWithin_mono _ (hgapD i.castSucc))
  have hright (i : Fin n) (u : ℝ)
      (hu : Tendsto f (𝓝[Ioo (gap i.succ).1 (gap i.succ).2]
        (gap i.succ).1) (𝓝 u)) : |value i - u| ≤ A i := by
    have : NeBot (𝓝[Ioo (gap i.succ).1 (gap i.succ).2] (gap i.succ).1) :=
      mem_closure_iff_nhdsWithin_neBot.mp (by
        rw [closure_Ioo (hgap i.succ).ne]
        exact left_mem_Icc.mpr (hgap i.succ).le)
    rw [abs_sub_comm]
    apply hcluster i (H i).2 u (right_mem_Icc.mpr (hinside i).2.1)
    simpa only [gap, gapsAfterHoles_succ_fst] using
      hu.mapClusterPt.mono (nhdsWithin_mono _ (hgapD i.succ))
  have hb := filled_gap_integration_bound n (fun i => (gap i).1) (fun i => (gap i).2)
    f d F value A φ C hgap
    (by intro i; simpa only [gap, gapsAfterHoles_castSucc_snd, gapsAfterHoles_succ_fst] using (hinside i).2.1)
    (fun i x hx => hd x (hgapD i hx)) hgi (fun i => hF.mono (hgapD i))
    (by
      intro i x hx
      apply hfill i
      simpa only [gap, gapsAfterHoles_castSucc_snd, gapsAfterHoles_succ_fst] using Ioo_subset_Icc_self hx)
    hφ (by simpa only [gap, gapsAfterHoles_zero_fst] using hzero)
    (by simpa only [gap, gapsAfterHoles_last_snd] using hone)
    hint hdint hC hA hleft hright (fun _ => hbound _) (fun _ => hbound _)
  simpa only [gap, gapsAfterHoles_zero_fst, gapsAfterHoles_last_snd] using hb

end CircleDomainRigidity

end OAI
