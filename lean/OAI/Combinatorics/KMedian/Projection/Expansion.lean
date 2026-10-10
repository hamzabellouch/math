import Mathlib
import OAI.Combinatorics.KMedian.Projection.Operator

namespace OAI

section Inline_PCPProjectionExpansion

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace MixedNorm
variable {U T : Type} [Fintype U] [Nonempty U] [Fintype T]
omit [Nonempty U] in
lemma sq_coordinates (f : U → T → ℝ) : sq f=∑ t, energy (fun u => f u t) := by
  unfold sq energy
  exact expect_sum_comm _ _ _

lemma sq_center (f : U → T → ℝ) :
    sq (fun u t => f u t-𝔼 v, f v t)=sq f-∑ t, (𝔼 u, f u t)^2 := by
  rw [sq_coordinates,sq_coordinates]
  simp_rw [energy_center]
  rw [sum_sub_distrib]

lemma sq_mean_le (f : U → T → ℝ) : ∑ t, (𝔼 u, f u t)^2 ≤ sq f := by
  rw [sq_coordinates]
  exact sum_le_sum (fun t _ => mean_sq_le_energy _)

lemma sq_le_uniform (f : U → T → ℝ) (M : ℝ) (h : ∀ u, ∑ t, f u t^2≤M) : sq f≤M := by
  unfold sq
  exact (expect_le_expect (fun u _ => h u)).trans_eq (Fintype.expect_const M)
end MixedNorm

namespace BiProjection
variable {U V D S A B T : Type}
variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B] [Fintype T]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S]
variable (G : BiProjection U V D S A B)

def Expands (γ : ℝ) : Prop := ∀ h : U → ℝ,
  energy (G.average h) ≤ (1-γ)*energy h+γ*(𝔼 u, h u)^2

omit [Fintype U] [Fintype D] [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] in
lemma collision_le_average (f : U → A → T → ℝ) (hf : ∀ u a t, 0 ≤ f u a t) :
    G.collision f ≤ MixedNorm.sq (fun v t => G.average (fun u => ∑ a, f u a t) v) := by
  unfold collision MixedNorm.sq
  simp only [Fintype.sum_prod_type]
  apply expect_le_expect
  intro v _
  rw [sum_comm]
  apply sum_le_sum
  intro t _
  have h := sum_sq_le_sq_sum_of_nonneg (s := (univ : Finset B))
    (fun b _ => G.push_nonneg f hf v b t)
  rwa [G.push_total] at h

omit [Fintype D] [Nonempty V] [Nonempty D] [Nonempty S] in
lemma collision_variance (γ : ℝ) (hG : G.Expands γ)
    (f : U → A → T → ℝ) (hf : ∀ u a t, 0 ≤ f u a t) :
    G.collision f ≤ MixedNorm.sq (fun u t => ∑ a, f u a t)-
      γ*MixedNorm.sq (fun u t => (∑ a, f u a t)-(𝔼 v, ∑ a, f v a t)) := by
  have h := sum_le_sum (fun t (_ : t ∈ (univ : Finset T)) => hG (fun u => ∑ a, f u a t))
  have hfirst := G.collision_le_average f hf
  rw [MixedNorm.sq_coordinates] at hfirst
  rw [sum_add_distrib,← mul_sum,← mul_sum] at h
  rw [MixedNorm.sq_center,MixedNorm.sq_coordinates]
  nlinarith only [hfirst,h]

omit [Fintype D] [Nonempty V] [Nonempty D] [Nonempty S] in
lemma variance_bound (γ : ℝ) (hG : G.Expands γ)
    (f : U → A → T → ℝ) (hf : ∀ u a t, 0 ≤ f u a t) (M : ℝ)
    (hm : ∀ u, ∑ t, (∑ a, f u a t)^2 ≤ M^2) :
    γ*MixedNorm.sq (fun u t => (∑ a, f u a t)-(𝔼 v, ∑ a, f v a t)) ≤
      M^2-G.collision f := by
  have h := G.collision_variance γ hG f hf
  have hh := MixedNorm.sq_le_uniform (fun u t => ∑ a, f u a t) (M^2) hm
  linarith

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionExpansion

end OAI
