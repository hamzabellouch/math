import OAI.GroupTheory.PolycyclicRecognition.Analysis.NormalizedPairPacking
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponential
import Mathlib.Topology.MetricSpace.Pseudo.Pi

namespace OAI

/-! # A normalized quasi-isometry preserves separated tuple counts -/

noncomputable section
namespace PolycyclicRecognition

open Metric Filter
open scoped NNReal Topology

variable {G : Type*} [Group G] [MetricSpace G] {Λ : ℝ≥0}

theorem normalizedPair_tuple_dist_gt_one {h : ℕ} (p : NormalizedPair G Λ)
    (hΛ : 0 < (Λ : ℝ)) {u v : Fin h → G}
    (huv : (Λ : ℝ) * ((Λ : ℝ) + 1) < dist u v) :
    1 < dist (fun i => p.val.1 (u i)) (fun i => p.val.1 (v i)) := by
  have hρ : 0 ≤ (Λ : ℝ) * ((Λ : ℝ) + 1) := by positivity
  have hi : ∃ i, (Λ : ℝ) * ((Λ : ℝ) + 1) < dist (u i) (v i) := by
    by_contra hn
    push Not at hn
    exact (not_le_of_gt huv) ((dist_pi_le_iff hρ).mpr hn)
  obtain ⟨i, hi⟩ := hi
  exact (normalizedPair_image_dist_gt_one p hΛ hi).trans_le
    (dist_le_pi_dist (fun i : Fin h => p.val.1 (u i)) (fun i : Fin h => p.val.1 (v i)) i)

variable [DecidableEq G]

theorem normalizedPair_tuple_image_card_separated {h : ℕ} (p : NormalizedPair G Λ)
    (hΛ : 0 < (Λ : ℝ)) (s : Finset (Fin h → G))
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (Λ : ℝ) * ((Λ : ℝ) + 1) < dist x y) :
    let t := s.image (fun u i => p.val.1 (u i))
    t.card = s.card ∧ ∀ x ∈ t, ∀ y ∈ t, x ≠ y → 1 ≤ dist x y := by
  classical
  dsimp only
  constructor
  · apply Finset.card_image_iff.mpr
    intro x hx y hy he
    by_contra hne
    have hd := normalizedPair_tuple_dist_gt_one p hΛ (hsep x hx y hy hne)
    dsimp only at he
    rw [he, dist_self] at hd
    linarith
  · intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    have huv : u ≠ v := fun he => hxy (congrArg (fun w i => p.val.1 (w i)) he)
    exact (normalizedPair_tuple_dist_gt_one p hΛ (hsep u hu v hv huv)).le

theorem normalizedPair_tuple_count_rate {h : ℕ} (p : ℕ → NormalizedPair G Λ)
    (hΛ : 0 < (Λ : ℝ)) (s : ℕ → Finset (Fin h → G))
    (hsep : ∀ n, ∀ x ∈ s n, ∀ y ∈ s n, x ≠ y →
      (Λ : ℝ) * ((Λ : ℝ) + 1) < dist x y)
    {scale : ℕ → ℝ} {a : ℝ}
    (hcount : HasSubexponentialLowerBoundSeq scale
      (fun n => ((s n).card : ℝ) / Real.exp (scale n * a))) :
    let t := fun n => (s n).image (fun u i => (p n).val.1 (u i))
    (∀ n, ∀ x ∈ t n, ∀ y ∈ t n, x ≠ y → 1 ≤ dist x y) ∧
      HasSubexponentialLowerBoundSeq scale
        (fun n => ((t n).card : ℝ) / Real.exp (scale n * a)) := by
  classical
  have ht (n : ℕ) := normalizedPair_tuple_image_card_separated (p n) hΛ (s n) (hsep n)
  exact ⟨fun n => (ht n).2, by simpa only [(ht _).1] using hcount⟩

end PolycyclicRecognition

end

end OAI
