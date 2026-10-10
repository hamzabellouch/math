import OAI.Analysis.CircleDomains.Modulus.NormalizedUniformBounds
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

namespace OAI

/-!
# Simultaneous limits of marked round disks

Bounded centers and nonnegative bounded radii form a compact parameter
space. A countable family therefore admits one subsequence on which all
parameters converge. The limiting radius may be zero.
-/

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_marked_disk_parameter_limits
    {B : Type*} [Countable B] {L : ℝ}
    (c : ℕ → B → ℂ) (r : ℕ → B → ℝ)
    (hc : ∀ n b, ‖c n b‖ ≤ L) (hr : ∀ n b, r n b ∈ Icc 0 L) :
    ∃ (s : ℕ → ℕ) (c₀ : B → ℂ) (r₀ : B → ℝ),
      StrictMono s ∧ (∀ b, ‖c₀ b‖ ≤ L ∧ r₀ b ∈ Icc 0 L) ∧
      (∀ b, Tendsto (fun n => c (s n) b) atTop (𝓝 (c₀ b))) ∧
      (∀ b, Tendsto (fun n => r (s n) b) atTop (𝓝 (r₀ b))) := by
  let P : Set (B → ℂ × ℝ) := pi univ (fun _ => closedBall (0 : ℂ) L ×ˢ Icc 0 L)
  have hP : IsCompact P := isCompact_univ_pi fun _ => (isCompact_closedBall 0 L).prod isCompact_Icc
  let v : ℕ → B → ℂ × ℝ := fun n b => (c n b, r n b)
  have hv : ∀ n, v n ∈ P := by
    intro n b _
    exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hc n b, hr n b⟩
  obtain ⟨v₀, hv₀, s, hs, hlim⟩ := hP.tendsto_subseq hv
  refine ⟨s, fun b => (v₀ b).1, fun b => (v₀ b).2, hs, ?_, ?_, ?_⟩
  · intro b
    have hb := hv₀ b (mem_univ b)
    exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hb.1, hb.2⟩
  · intro b
    exact (continuous_fst.tendsto (v₀ b)).comp (tendsto_pi_nhds.mp hlim b)
  · intro b
    exact (continuous_snd.tendsto (v₀ b)).comp (tendsto_pi_nhds.mp hlim b)

theorem closedBall_eq_affine_image {r : ℝ} (hr : 0 ≤ r) (c : ℂ) :
    closedBall c r = (fun u : ℂ => c + r • u) '' closedBall 0 1 := by
  rw [← affinity_unitClosedBall hr c]
  change (fun z : ℂ => c + z) '' ((fun u : ℂ => r • u) '' closedBall 0 1) = _
  rw [image_image]

theorem exists_closedBall_point_dist_le
    {c d x : ℂ} {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hx : x ∈ closedBall c r) :
    ∃ y ∈ closedBall d s, dist x y ≤ dist c d + |r - s| := by
  rw [closedBall_eq_affine_image hr c] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  refine ⟨d + s • u, ?_, ?_⟩
  · rw [closedBall_eq_affine_image hs d]
    exact mem_image_of_mem _ hu
  · have hu' : ‖u‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hu
    have heq : c + r • u - (d + s • u) = (c - d) + (r - s) • u := by
      rw [sub_smul]
      abel
    calc
      dist (c + r • u) (d + s • u) = ‖(c - d) + (r - s) • u‖ := by
        rw [dist_eq_norm, heq]
      _ ≤ ‖c - d‖ + ‖(r - s) • u‖ := norm_add_le _ _
      _ ≤ dist c d + |r - s| := by
        rw [norm_smul, Real.norm_eq_abs, dist_eq_norm]
        nlinarith [abs_nonneg (r - s)]

theorem hausdorffDist_closedBall_le_parameters
    {c d : ℂ} {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    hausdorffDist (closedBall c r) (closedBall d s) ≤ dist c d + |r - s| := by
  refine hausdorffDist_le_of_mem_dist (by positivity)
    (fun _ hx => exists_closedBall_point_dist_le hr hs hx) ?_
  intro y hy
  simpa only [dist_comm d c, abs_sub_comm s r] using
    exists_closedBall_point_dist_le (d := c) hs hr hy

theorem tendsto_hausdorffDist_closedBall
    {c : ℕ → ℂ} {r : ℕ → ℝ} {c₀ : ℂ} {r₀ : ℝ}
    (hr : ∀ n, 0 ≤ r n) (hr₀ : 0 ≤ r₀)
    (hc : Tendsto c atTop (𝓝 c₀)) (hlim : Tendsto r atTop (𝓝 r₀)) :
    Tendsto (fun n => hausdorffDist (closedBall (c n) (r n)) (closedBall c₀ r₀))
      atTop (𝓝 0) := by
  have hb : Tendsto (fun n => dist (c n) c₀ + |r n - r₀|) atTop (𝓝 0) := by
    simpa only [dist_self, sub_self, abs_zero, add_zero] using
      (hc.dist (tendsto_const_nhds (x := c₀))).add
        ((hlim.sub (tendsto_const_nhds (x := r₀))).abs)
  exact squeeze_zero (fun _ => hausdorffDist_nonneg)
    (fun n => hausdorffDist_closedBall_le_parameters (hr n) hr₀) hb

/-- One subsequence gives Hausdorff limits for every marked disk. -/
theorem exists_marked_disk_hausdorff_limits
    {B : Type*} [Countable B] {L : ℝ}
    (c : ℕ → B → ℂ) (r : ℕ → B → ℝ)
    (hc : ∀ n b, ‖c n b‖ ≤ L) (hr : ∀ n b, r n b ∈ Icc 0 L) :
    ∃ (s : ℕ → ℕ) (c₀ : B → ℂ) (r₀ : B → ℝ),
      StrictMono s ∧ (∀ b, ‖c₀ b‖ ≤ L ∧ r₀ b ∈ Icc 0 L) ∧
      ∀ b, Tendsto (fun n => hausdorffDist (closedBall (c (s n) b) (r (s n) b))
        (closedBall (c₀ b) (r₀ b))) atTop (𝓝 0) := by
  obtain ⟨s, c₀, r₀, hs, hb, hclim, hrlim⟩ :=
    exists_marked_disk_parameter_limits c r hc hr
  exact ⟨s, c₀, r₀, hs, hb, fun b => tendsto_hausdorffDist_closedBall
    (fun n => (hr (s n) b).1) (hb b).2.1 (hclim b) (hrlim b)⟩

end CircleDomainRigidity

end

end OAI
