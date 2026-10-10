import OAI.Analysis.CircleDomains.Sobolev.PlanarGradientDensity
import Mathlib.Topology.Order.Compact

namespace OAI

/-!
# Crossing segments from nested bounded regions

On any horizontal line meeting the inner region, the leftmost points of
the inner and outer closures lie on their frontiers. Strict containment
puts the outer point strictly to the left. Thus prescribed zero/one
frontier values provide the crossing segments needed by line payment.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_leftmost_horizontal_frontier
    {U : Set ℂ} (hU : IsOpen U) (hcompact : IsCompact (closure U))
    {y : ℝ} (hne : ∃ z ∈ closure U, z.im = y) :
    ∃ x : ℝ, horizontalLine y x ∈ frontier U ∧
      ∀ z ∈ closure U, z.im = y → x ≤ z.re := by
  let K := closure U ∩ {z : ℂ | z.im = y}
  have hK : IsCompact K := hcompact.inter_right (isClosed_eq Complex.continuous_im continuous_const)
  have hKne : K.Nonempty := by
    obtain ⟨z, hz, hy⟩ := hne
    exact ⟨z, hz, hy⟩
  obtain ⟨x, hx⟩ := (hK.image Complex.continuous_re).exists_isLeast (hKne.image Complex.re)
  obtain ⟨p, hp, hpx⟩ := hx.1
  have hpeq : p = horizontalLine y x := by
    apply Complex.ext
    · exact hpx
    · exact hp.2
  have hxclosure : horizontalLine y x ∈ closure U := hpeq ▸ hp.1
  have hmin : ∀ z ∈ closure U, z.im = y → x ≤ z.re := by
    intro z hz hy
    exact hx.2 (mem_image_of_mem _ ⟨hz, hy⟩)
  have hxnot : horizontalLine y x ∉ U := by
    intro hxU
    have hpre : (horizontalLine y) ⁻¹' U ∈ 𝓝 x :=
      (hU.preimage (continuous_horizontalLine y)).mem_nhds hxU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
    have hnear : x - ε / 2 ∈ ball x ε := by
      rw [mem_ball, Real.dist_eq]
      rw [show x - ε / 2 - x = -(ε / 2) by ring, abs_neg, abs_of_pos (half_pos hε)]
      linarith
    have hback : horizontalLine y (x - ε / 2) ∈ U := hball hnear
    have hbound := hmin (horizontalLine y (x - ε / 2)) (subset_closure hback) rfl
    change x ≤ x - ε / 2 at hbound
    linarith
  refine ⟨x, ?_, hmin⟩
  rw [frontier, hU.interior_eq]
  exact ⟨hxclosure, hxnot⟩

theorem exists_horizontal_frontier_crossing
    {W U : Set ℂ} (hW : IsOpen W) (hU : IsOpen U)
    (hWcompact : IsCompact (closure W)) (hUcompact : IsCompact (closure U))
    (hWU : closure W ⊆ U) {y : ℝ} (hne : ∃ z ∈ closure W, z.im = y) :
    ∃ a b : ℝ, a < b ∧ horizontalLine y a ∈ frontier U ∧
      horizontalLine y b ∈ frontier W := by
  obtain ⟨b, hb, hminb⟩ := exists_leftmost_horizontal_frontier hW hWcompact hne
  have hbU : horizontalLine y b ∈ U := hWU (frontier_subset_closure hb)
  obtain ⟨a, ha, hmina⟩ := exists_leftmost_horizontal_frontier hU hUcompact
    ⟨horizontalLine y b, subset_closure hbU, rfl⟩
  refine ⟨a, b, ?_, ha, hb⟩
  have hab : a ≤ b := hmina _ (subset_closure hbU) rfl
  apply lt_of_le_of_ne hab
  intro he
  have haU : horizontalLine y a ∈ U := he.symm ▸ hbU
  have hnot : horizontalLine y a ∉ U := by
    simpa only [horizontalLine, hU.interior_eq] using ha.2
  exact hnot haU

theorem horizontal_frontier_crossings_give_values
    {W U D : Set ℂ} (hW : IsOpen W) (hU : IsOpen U)
    (hWcompact : IsCompact (closure W)) (hUcompact : IsCompact (closure U))
    (hWU : closure W ⊆ U) {L : ℝ} (hUL : closure U ⊆ closedBall 0 L)
    (hUD : frontier U ⊆ D) (hWD : frontier W ⊆ D)
    {v : ℂ → ℝ} (hzero : ∀ z ∈ frontier U, v z = 0)
    (hone : ∀ z ∈ frontier W, v z = 1) {J : Set ℝ}
    (hJ : J ⊆ Complex.im '' closure W) :
    ∀ y ∈ J, ∃ a b : ℝ, a < b ∧ horizontalLine y a ∈ D ∧
      horizontalLine y b ∈ D ∧ horizontalLine y a ∈ closedBall 0 L ∧
      horizontalLine y b ∈ closedBall 0 L ∧ v (horizontalLine y a) = 0 ∧
      v (horizontalLine y b) = 1 := by
  intro y hy
  obtain ⟨z, hz, hzy⟩ := hJ hy
  obtain ⟨a, b, hab, ha, hb⟩ := exists_horizontal_frontier_crossing hW hU hWcompact hUcompact
    hWU ⟨z, hz, hzy⟩
  exact ⟨a, b, hab, hUD ha, hWD hb, hUL (frontier_subset_closure ha),
    hUL (subset_closure (hWU (frontier_subset_closure hb))), hzero _ ha, hone _ hb⟩

end CircleDomainRigidity

end

end OAI
