import Mathlib
import OAI.Combinatorics.KMedian.Projection.Contraction
import OAI.Combinatorics.KMedian.Projection.Expansion
import OAI.Combinatorics.KMedian.Projection.Rounding

namespace OAI

section Inline_PCPProjectionBound

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace MixedNorm
lemma selected_le {V T : Type} [Fintype V] [Fintype T] [Nonempty V]
    (f : V → T → ℝ) (g : V → T) : energy (fun v => f v (g v)) ≤ sq f := by
  unfold energy sq
  apply expect_le_expect
  intro v _
  exact single_le_sum (fun t _ => _root_.sq_nonneg (f v t)) (mem_univ (g v))
end MixedNorm

namespace BiProjection
variable {U V D S A B : Type}
variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
variable (G : BiProjection U V D S A B)

def CollisionBound (r : ℝ) : Prop := ∀ (T : Type) [Fintype T]
  (f : U → A → T → ℝ), (∀ u a t, 0 ≤ f u a t) → ∀ M : ℝ, 0 ≤ M →
  (∀ u, ∑ t, (∑ a, f u a t)^2≤M) → G.collision f≤r*M

lemma collisionBound_of_expansion (s γ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hs : G.Sound s) (hG : G.Expands γ) :
    G.CollisionBound (1-γ*((1-s)/4)^2) := by
  intro T _ f hf M hM hm
  have hh := G.collision_contraction s γ hs0 hs1 hγ0 hγ1 hs hG f hf
    (Real.sqrt M) (Real.sqrt_nonneg M) (by simpa only [Real.sq_sqrt hM] using hm)
  simpa only [Real.sq_sqrt hM] using hh

omit [Nonempty V] [Nonempty A] [Nonempty B] in
lemma collisionBound_one : G.CollisionBound 1 := by
  intro T _ f hf M hM hm
  have hh := G.collision_le_abs_total f
  simp only [abs_of_nonneg (hf _ _ _)] at hh
  simpa only [one_mul] using hh.trans (MixedNorm.sq_le_uniform _ M hm)

omit [Fintype V] [Fintype S] [Fintype A] [Fintype B]
  [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B] in
lemma score_nonneg (a : U → A) (b : V → B) : 0 ≤ G.score a b := by
  unfold score
  exact expect_nonneg (fun _ _ => expect_nonneg (fun _ _ => by split_ifs <;> norm_num))

noncomputable def pointLabel (a : U → A) : U → A → Unit → ℝ := fun u c _ => if c=a u then 1 else 0
omit [Fintype U] [Fintype A] [Nonempty U] [Nonempty A] in
lemma pointLabel_nonneg (a : U → A) : ∀ u c t, 0 ≤ pointLabel a u c t := by
  intros
  unfold pointLabel
  split_ifs <;> norm_num
omit [Fintype U] [Nonempty U] [Nonempty A] in
lemma pointLabel_total (a : U → A) (u : U) : ∑ c, pointLabel a u c ()=1 := by simp [pointLabel]

omit [Fintype B] [Nonempty U] [Nonempty V] [Nonempty D]
  [Nonempty S] [Nonempty A] [Nonempty B] in
lemma score_eq_push (a : U → A) (b : V → B) :
    G.score a b=(𝔼 v, G.push (pointLabel a) v (b v) ()) := by
  have hh := G.fractional_score_reindex (fun u c => pointLabel a u c ()) b
  simp only [pointLabel] at hh
  simp only [ite_mul,one_mul,zero_mul,sum_ite_eq',mem_univ,ite_true] at hh
  exact hh.symm

omit [Nonempty U] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B] in
lemma score_sq_le_collision (a : U → A) (b : V → B) :
    G.score a b^2≤G.collision (pointLabel a) := by
  rw [G.score_eq_push]
  calc
    _ ≤ energy (fun v => G.push (pointLabel a) v (b v) ()) := mean_sq_le_energy _
    _ ≤ G.collision (pointLabel a) :=
      MixedNorm.selected_le (fun v (p : B × Unit) => G.push (pointLabel a) v p.1 p.2)
        (fun v => (b v,()))

omit [Nonempty U] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B] in
lemma sound_of_collisionBound (r ε : ℝ) (hr : G.CollisionBound r) (hε : 0 ≤ ε)
    (he : r≤ε^2) : G.Sound ε := by
  intro a b
  have hp := hr Unit (pointLabel a) (pointLabel_nonneg a) 1 (by norm_num) (by
    intro u
    simp [pointLabel])
  have hq := (G.score_sq_le_collision a b).trans hp
  simp only [mul_one] at hq
  nlinarith [G.score_nonneg a b]

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionBound

end OAI
