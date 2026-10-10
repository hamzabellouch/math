import OAI.MeasureTheory.Falconer.Estimates.PlanarPrefixTruncation
import OAI.MeasureTheory.Falconer.Recursion.LocalProfileRegularity

namespace OAI

/-! Prefix ratios for the actual endpoint cells of a profile interval.
Both endpoint binning losses are retained explicitly. -/
namespace Falconer.Regularization
attribute [local instance] Classical.propDecidable

theorem planar_prefixFiber_children_subset (C : Finset (CellPath 2)) {a b n : ℕ}
    (hnb : n ≤ b) (p q : CellPath 2) :
    prefixFiber (prefixChildren C a b p) n q ⊆ prefixChildren C n b q := by
  intro v hv
  obtain ⟨hv,hvq⟩ := Finset.mem_filter.mp hv
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
  have hn : w.take n = q := by
    simpa only [List.take_take,Nat.min_eq_left hnb] using hvq
  exact Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,hn⟩,rfl⟩

theorem blockClass_truncated_fiber_ratio {N : ℕ} {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (B : ℕ) (f : CellPath 2 → List ℕ) (K : ℕ)
    (p : CellPath 2) {i j k : ℕ} (hjk : j ≤ k) (hki : k ≤ i) (hi : i ≤ K)
    {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B i)))
    {q : CellPath 2}
    (hq : q ∈ (prefixChildren
      (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
      (blockDepth N B i) (blockDepth N B j) p₀).image (List.take (blockDepth N B k))) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    let D := prefixChildren C (blockDepth N B i) (blockDepth N B j) p₀
    ((prefixFiber D (blockDepth N B k) q).card:ℝ)/(D.card:ℝ) ≤
      (2:ℝ)^(k+j)*((blockProduct L F N B k p:ℝ)/(blockProduct L F N B i p:ℝ)) := by
  let F := blockLabel L N B f K
  let C := classLeaves L F (F p)
  let D := prefixChildren C (blockDepth N B i) (blockDepth N B j) p₀
  have hDsub : D ⊆ C.image (List.take (blockDepth N B j)) :=
    Finset.image_subset_image (Finset.filter_subset _ _)
  have hq' : q ∈ C.image (List.take (blockDepth N B k)) := by
    rw [← planar_prefix_image_take_take C (blockDepth_antitone N B hjk)]
    exact Finset.image_subset_image hDsub hq
  have hparent := (blockClass_descendant_count hL B f K p (hjk.trans hki) hi hp₀).1
  have hchild := (blockClass_descendant_count hL B f K p hjk (hki.trans hi) hq').2
  have hsub := planar_prefixFiber_children_subset C (a := blockDepth N B i)
    (blockDepth_antitone N B hjk) p₀ q
  have hi0 : 0 < (blockProduct L F N B i p:ℝ) := Nat.cast_pos.mpr (blockProduct_pos _ _ _ _ _ _)
  have hj0 : 0 < (blockProduct L F N B j p:ℝ) := Nat.cast_pos.mpr (blockProduct_pos _ _ _ _ _ _)
  have hk0 : 0 < (blockProduct L F N B k p:ℝ) := Nat.cast_pos.mpr (blockProduct_pos _ _ _ _ _ _)
  have hlow : 0 < ((blockProduct L F N B i p:ℝ)/(blockProduct L F N B j p:ℝ))/(2:ℝ)^j := by positivity
  have hbound : ((prefixFiber D (blockDepth N B k) q).card:ℝ) ≤
      (2:ℝ)^k*((blockProduct L F N B k p:ℝ)/(blockProduct L F N B j p:ℝ)) :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hchild
  change ((prefixFiber D (blockDepth N B k) q).card:ℝ)/(D.card:ℝ) ≤
    (2:ℝ)^(k+j)*((blockProduct L F N B k p:ℝ)/(blockProduct L F N B i p:ℝ))
  calc
    _ ≤ ((2:ℝ)^k*((blockProduct L F N B k p:ℝ)/(blockProduct L F N B j p:ℝ)))/
        (((blockProduct L F N B i p:ℝ)/(blockProduct L F N B j p:ℝ))/(2:ℝ)^j) :=
      div_le_div₀ (by positivity) hbound hlow hparent
    _ = _ := by rw [pow_add]; field_simp

theorem blockClass_truncated_frostman {N : ℕ} (hN : 0 < N) {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (B : ℕ) (f : CellPath 2 → List ℕ) (K : ℕ)
    (p : CellPath 2) {i j k : ℕ} (hjk : j ≤ k) (hki : k ≤ i) (hi : i ≤ K)
    {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B i)))
    {q : CellPath 2}
    (hq : q ∈ (prefixChildren
      (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
      (blockDepth N B i) (blockDepth N B j) p₀).image (List.take (blockDepth N B k)))
    {s A : ℝ}
    (hprofile : let F := blockLabel L N B f K
      s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))-A ≤
        (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
          regularizedProfile L F N B K p (blockDepth N B i))) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    let D := prefixChildren C (blockDepth N B i) (blockDepth N B j) p₀
    ((prefixFiber D (blockDepth N B k) q).card:ℝ)/(D.card:ℝ) ≤
      (2:ℝ)^(k+j)*(2:ℝ)^(A-s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))) := by
  have hb := blockClass_truncated_fiber_ratio hL B f K p hjk hki hi hp₀ hq
  dsimp only at hb ⊢
  rw [blockProduct_relative_profile hN hL _ B K p (hki.trans hi) hi] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  dsimp only at hprofile
  linarith

end Falconer.Regularization

end OAI
