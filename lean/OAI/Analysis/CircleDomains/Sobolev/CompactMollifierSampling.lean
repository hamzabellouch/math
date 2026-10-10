import OAI.Analysis.CircleDomains.Sobolev.PositiveSobolevApproximation
import Mathlib.Geometry.Manifold.PartitionOfUnity

namespace OAI

/-! Uniform sampling control on compact sets, including exact preservation
of constant regions and smooth cutoffs equal to one near a compact set. -/

open Set Filter MeasureTheory Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem planarMollifier_samples_eventually
    {K V : Set EuclideanPlane} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∀ᶠ n in atTop, ∀x ∈ K,
      ball x (DeGiorgi.shrinkingBump (d := 2) n).rOut ⊆ V := by
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hV hKV
  have hr : ∀ᶠ n in atTop, (DeGiorgi.shrinkingBump (d := 2) n).rOut < δ :=
    (tendsto_order.1 tendsto_planarMollifier_radius).2 δ hδ
  filter_upwards [hr] with n hn x hx y hy
  apply hδV
  exact mem_cthickening_of_dist_le y x δ K hx
    ((mem_ball.1 hy).le.trans hn.le)

theorem planarMollification_mem_Icc_on_compact_eventually
    {u : EuclideanPlane → ℝ} (hu : AEStronglyMeasurable u volume)
    {K V : Set EuclideanPlane} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    {a b : ℝ} (hb : ∀y ∈ V, u y ∈ Icc a b) :
    ∀ᶠ n in atTop, ∀x ∈ K, planarMollification u n x ∈ Icc a b := by
  filter_upwards [planarMollifier_samples_eventually hK hV hKV] with n hn x hx
  exact normed_convolution_mem_Icc volume (DeGiorgi.shrinkingBump n) hu
    (fun y hy => hb y (hn x hx hy))

theorem planarMollification_eq_on_compact_eventually
    {u : EuclideanPlane → ℝ} {K V : Set EuclideanPlane}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    {c : ℝ} (hc : ∀y ∈ V, u y = c) :
    ∀ᶠ n in atTop, ∀x ∈ K, planarMollification u n x = c := by
  filter_upwards [planarMollifier_samples_eventually hK hV hKV] with n hn x hx
  exact normed_convolution_eq_of_constant volume (DeGiorgi.shrinkingBump n)
    (fun y hy => hc y (hn x hx hy))

theorem exists_smooth_compact_cutoff_one_near
    {K Ω : Set EuclideanPlane} (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    ∃ (η : EuclideanPlane → ℝ) (V : Set EuclideanPlane),
      ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
      (∀x, η x ∈ Icc 0 1) ∧ tsupport η ⊆ Ω ∧
      IsOpen V ∧ K ⊆ V ∧ ∀x ∈ V, η x = 1 := by
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  have hsub : cthickening (δ / 2) K ⊆ thickening δ K :=
    cthickening_subset_thickening' hδ (half_lt_self hδ) K
  obtain ⟨η, hη, hunit, hsupp, hone⟩ :=
    exists_contDiff_support_eq_eq_one_iff isOpen_thickening isClosed_cthickening hsub
      (n := (⊤ : ℕ∞))
  have hs : tsupport η ⊆ cthickening δ K := by
    rw [tsupport, hsupp]
    exact closure_thickening_subset_cthickening δ K
  refine ⟨η, thickening (δ / 2) K, hη,
    (hK.cthickening (r := δ)).of_isClosed_subset isClosed_closure hs,
    fun x => hunit (mem_range_self x), hs.trans hδΩ, isOpen_thickening,
    self_subset_thickening (half_pos hδ) K, ?_⟩
  intro x hx
  exact (hone x).1 (thickening_subset_cthickening (δ / 2) K hx)

end CircleDomainRigidity

end

end OAI
