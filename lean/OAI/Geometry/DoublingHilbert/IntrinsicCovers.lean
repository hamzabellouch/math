import Mathlib
import OAI.Geometry.DoublingHilbert.CompactModel

namespace OAI

open Set Metric
open scoped BigOperators
noncomputable section
namespace CompactBanach

def AmbientDoubling {B : Type*} [MetricSpace B] (K : Set B) (bound : ℕ) : Prop :=
  ∀ x ∈ K, ∀ r : ℝ, 0 < r →
    ∃ centers : Finset B, (∀ c ∈ centers, c ∈ K) ∧ centers.card ≤ bound ∧
      ∀ y ∈ K, dist y x < r → ∃ c ∈ centers, dist y c < r / 2

theorem doubling_iff_ambient {B : Type*} [MetricSpace B] {K : Set B} {bound : ℕ} :
    DoublingAtMost K bound ↔ AmbientDoubling K bound := by
  classical
  constructor
  · intro h x hx r hr
    obtain ⟨c, hc, hcov⟩ := h ⟨x, hx⟩ r hr
    refine ⟨c.image Subtype.val, ?_, (Finset.card_image_le).trans hc, ?_⟩
    · intro z hz
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hz
      exact w.property
    · intro y hy hxy
      obtain ⟨z, hz, hzy⟩ := hcov ⟨y, hy⟩ hxy
      exact ⟨z, Finset.mem_image.mpr ⟨z, hz, rfl⟩, hzy⟩
  · intro h x r hr
    obtain ⟨c, hc, hcard, hcov⟩ := h x x.property r hr
    let cs : Finset K := c.attach.image fun z => ⟨z.val, hc z.val z.property⟩
    refine ⟨cs, ?_, ?_⟩
    · exact (Finset.card_image_le).trans (by simpa using hcard)
    · intro y hxy
      obtain ⟨z, hz, hzy⟩ := hcov y y.property hxy
      refine ⟨⟨z, hc z hz⟩, ?_, hzy⟩
      exact Finset.mem_image.mpr ⟨⟨z, hz⟩, Finset.mem_attach _ _, rfl⟩

                                                                                    
theorem ambient_iterated_cover {B : Type*} [MetricSpace B] {K : Set B} {L : ℕ}
    (h : AmbientDoubling K L) (n : ℕ) {x : B} (hx : x ∈ K) {r : ℝ} (hr : 0 < r) :
    ∃ centers : Finset B, (∀ c ∈ centers, c ∈ K) ∧ centers.card ≤ L ^ n ∧
      ∀ y ∈ K, dist y x < r → ∃ c ∈ centers, dist y c < r / (2 : ℝ) ^ n := by
  classical
  induction n generalizing x r with
  | zero =>
    refine ⟨{x}, ?_, ?_, ?_⟩
    · simpa only [Finset.mem_singleton, forall_eq] using hx
    · simp
    · intro y _ hy
      exact ⟨x, by simp, by simpa using hy⟩
  | succ n ih =>
    obtain ⟨c, hc, hcard, hcov⟩ := h x hx r hr
    have H (z : c) := ih (hc z z.property) (half_pos hr)
    choose d hdK hdcard hdcov using H
    let cs : Finset B := c.attach.biUnion d
    refine ⟨cs, ?_, ?_, ?_⟩
    · intro z hz
      obtain ⟨w, _, hzw⟩ := Finset.mem_biUnion.mp hz
      exact hdK w z hzw
    · calc
        cs.card ≤ ∑ z ∈ c.attach, (d z).card := Finset.card_biUnion_le
        _ ≤ ∑ _z ∈ c.attach, L ^ n := Finset.sum_le_sum fun z _ => hdcard z
        _ = c.card * L ^ n := by simp
        _ ≤ L * L ^ n := Nat.mul_le_mul_right _ hcard
        _ = L ^ (n + 1) := (pow_succ' _ _).symm
    · intro y hy hxy
      obtain ⟨z, hz, hyz⟩ := hcov y hy hxy
      obtain ⟨w, hw, hyw⟩ := hdcov ⟨z, hz⟩ y hy hyz
      refine ⟨w, Finset.mem_biUnion.mpr ⟨⟨z, hz⟩, Finset.mem_attach _ _, hw⟩, ?_⟩
      simpa only [div_div, pow_succ'] using hyw

end CompactBanach
end

end OAI
