import Mathlib
import OAI.Combinatorics.KMedian.Projection.Bound
import OAI.Combinatorics.KMedian.Projection.Product

namespace OAI

section Inline_PCPProjectionTensor

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {U V D S A B U' V' D' S' A' B' T : Type}
variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
variable [Fintype U'] [Fintype V'] [Fintype D'] [Fintype S'] [Fintype A'] [Fintype B']
variable [Fintype T]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
variable [Nonempty U'] [Nonempty V'] [Nonempty D'] [Nonempty S'] [Nonempty A'] [Nonempty B']
variable (G : BiProjection U V D S A B) (H : BiProjection U' V' D' S' A' B')

omit [Fintype U] [Fintype U'] [Fintype D'] [Nonempty U] [Nonempty A]
  [Nonempty U'] [Nonempty D'] [Nonempty S'] [Nonempty A'] [Nonempty B'] in
lemma partialPush_budget (r M : ℝ) (hr : H.CollisionBound r)
    (f : (U × U') → (A × A') → T → ℝ) (hf : ∀ u a t, 0 ≤ f u a t)
    (hM : 0 ≤ M) (hm : ∀ u, ∑ t, (∑ a, f u a t)^2≤M) (u : U) :
    (∑ z, (∑ a, H.partialPush f u a z)^2) ≤ (Fintype.card V':ℝ)*(r*M) := by
  let g : U' → A' → T → ℝ := fun u' a' t => ∑ a, f (u,u') (a,a') t
  have hg : ∀ u' a' t, 0 ≤ g u' a' t := fun u' a' t => sum_nonneg (fun a _ => hf _ _ _)
  have hgM : ∀ u', ∑ t, (∑ a', g u' a' t)^2≤M := by
    intro u'
    have hh := hm (u,u')
    simp only [Fintype.sum_prod_type] at hh
    change (∑ t, (∑ a', ∑ a, f (u,u') (a,a') t)^2)≤M
    convert hh using 1
    apply sum_congr rfl
    intro t _
    congr 1
    exact sum_comm
  have h := hr T g hg M hM hgM
  have he : (∑ z, (∑ a, H.partialPush f u a z)^2) =
      (Fintype.card V':ℝ)*H.collision g := by
    simp_rw [H.partialPush_total]
    unfold collision MixedNorm.sq
    rw [Fintype.expect_eq_sum_div_card,mul_div_cancel₀ _ (show (Fintype.card V':ℝ) ≠ 0 by positivity)]
    simp only [Fintype.sum_prod_type,g]
  rw [he]
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)

omit [Fintype U] [Fintype D] [Fintype U'] [Fintype D']
  [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
  [Nonempty U'] [Nonempty D'] [Nonempty S'] [Nonempty A'] [Nonempty B'] in
lemma collisionBound_prod (r s : ℝ) (_hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hr : G.CollisionBound r) (hs : H.CollisionBound s) :
    (G.prod H).CollisionBound (r*s) := by
  intro T _ f hf M hM hm
  have h := hr (V' × (B' × T)) (H.partialPush f) (H.partialPush_nonneg f hf)
    ((Fintype.card V':ℝ)*(s*M)) (by positivity) (H.partialPush_budget s M hs f hf hM hm)
  rw [← G.prod_collision H f] at h
  apply (mul_le_mul_iff_left₀ (show 0 < (Fintype.card V':ℝ) by positivity)).mp
  nlinarith only [h]

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionTensor

end OAI
