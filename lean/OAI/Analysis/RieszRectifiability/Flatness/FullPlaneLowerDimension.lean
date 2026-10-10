import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.ADCoreMassPacking
import OAI.Analysis.RieszRectifiability.Nets.SeparatedEuclideanCover

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Module
open scoped ENNReal

theorem isometric_separated_AD_card_bound {n k d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (L : Ambient k →ₗᵢ[ℝ] Ambient d) (s : Finset (Ambient k))
    (hs : ∀ x ∈ s, ‖x‖ ≤ 1) (hsupp : ∀ x ∈ s, L x ∈ μ.support)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ dist x y) :
    (s.card : ℝ) * δ ^ n ≤ (G * 2 ^ n) * (2 ^ n * C) := by
  have hsub : ∀ x ∈ s, ball (L x) (δ / 2) ⊆ ball (0 : Ambient d) 2 := by
    intro x hx
    apply ball_subset_ball'
    rw [dist_zero_right, L.norm_map]
    linarith [hs x hx]
  have hd : Set.PairwiseDisjoint (s : Set (Ambient k)) (fun x => ball (L x) (δ / 2)) := by
    intro x hx y hy hxy
    apply ball_disjoint_ball
    rw [L.dist_map]
    linarith [hsep x hx y hy hxy]
  have hb := finite_disjoint_core_mass_bound n G μ hg s L (fun _ => δ / 2)
    (fun _ => (δ / 2) ^ n / C) (fun _ _ => by positivity)
    (fun x hx => hlower (L x) (hsupp x hx) (δ / 2) (by positivity))
    0 2 (by norm_num) hsub hd
  simp only [Finset.sum_const, nsmul_eq_mul] at hb
  have hbdiv : (s.card : ℝ) * δ ^ n / (2 ^ n * C) ≤ G * 2 ^ n := by
    convert! hb using 1
    rw [div_pow]
    field_simp
  exact (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ n * C)).mp hbdiv

theorem isometric_ball_in_support_dimension_le {n k d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (L : Ambient k →ₗᵢ[ℝ] Ambient d)
    (hsupp : ∀ x : Ambient k, ‖x‖ ≤ 1 → L x ∈ μ.support) : k ≤ n := by
  by_contra hnot
  have hnk : n < k := lt_of_not_ge hnot
  let M : ℝ := (G * 2 ^ n) * (2 ^ n * C)
  have hM : 0 ≤ M := by dsimp only [M]; positivity [hg.1]
  let δ : ℝ := min 1 (1 / (2 * (M + 1)))
  have hden : 0 < 2 * (M + 1) := by positivity
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos zero_lt_one hden)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδsmall : M * δ < 1 := by
    have ht : δ * (2 * (M + 1)) ≤ 1 := (le_div_iff₀ hden).mp (min_le_right _ _)
    nlinarith
  obtain ⟨s, hs, hsep, hcover⟩ := exists_separated_euclidean_closedBall_cover (k := k) 1 δ hδ
  have hcard := isometric_separated_AD_card_bound μ C G hC hg hlower L s hs
    (fun x hx => hsupp x (hs x hx)) δ hδ hδ1 hsep
  have hvol := euclidean_unit_ball_cover_card_lower s δ hδ (fun x hx => hcover x hx.le)
  have hp : δ ^ (k - n) ≤ δ := by
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k - n ≠ 0)
    rw [hq, pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hδ.le hδ1) hδ.le).trans_eq (one_mul δ)
  have hid : δ ^ k = δ ^ n * δ ^ (k - n) := by
    rw [← pow_add, Nat.add_sub_of_le hnk.le]
  have hupper : (s.card : ℝ) * δ ^ k ≤ M * δ := by
    rw [hid, ← mul_assoc]
    exact (mul_le_mul_of_nonneg_right hcard (pow_nonneg hδ.le (k - n))).trans
      (mul_le_mul_of_nonneg_left hp hM)
  exact (not_lt_of_ge (hvol.trans hupper)) hδsmall

theorem full_support_submodule_finrank_le {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (P : Submodule ℝ (Ambient d)) (hP : μ.support = (P : Set (Ambient d))) :
    Module.finrank ℝ P ≤ n := by
  obtain ⟨L, hL⟩ := exists_isometry_onto_subspace P rfl
  apply isometric_ball_in_support_dimension_le μ C G hC hg hlower L
  intro x _
  rw [hP]
  have hx : L x ∈ L.toLinearMap.range := LinearMap.mem_range_self L.toLinearMap x
  simpa only [hL] using! hx

end

end RieszRectifiability

end OAI
