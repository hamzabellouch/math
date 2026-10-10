import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.RealFilling

namespace OAI

namespace MetricKMedianRecovery.Completion

lemma convex_surrogate_upper {P E R : Type*} [Fintype P] [Fintype R]
    (K : ℝ) (q : ℕ) (base : P → ℝ) (distance : P → E → ℝ)
    (weight redBase : R → ℝ) (redDistance : R → E → ℝ)
    (theta : ℝ) (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1)
    (T : Finset R) (hT : T.card = q) (X : Finset E) :
    theta * surrogate K q base distance weight redBase redDistance ∅ +
      (1-theta) * surrogate K q base distance weight redBase redDistance X ≤
    K + (∑ p : P, (theta*base p + (1-theta)*cappedCost (base p) (distance p) X : ℝ)) +
      ∑ r ∈ T, weight r * (theta*redBase r +
        (1-theta)*cappedCost (redBase r) (redDistance r) X) := by
  have hq : q ≤ Fintype.card R := hT ▸ Finset.card_le_univ T
  have hc : T.card = min q (Fintype.card R) := by rw [min_eq_left hq, hT]
  have h₀ := mul_le_mul_of_nonneg_left
    (bottomSum_le (fun r => weight r * redBase r) hc) ht0
  have h₁ := mul_le_mul_of_nonneg_left
    (bottomSum_le (fun r => weight r * cappedCost (redBase r) (redDistance r) X) hc)
    (show 0 ≤ 1-theta by linarith)
  simp only [surrogate, cappedCost_empty]
  simp only [Finset.sum_add_distrib]
  have he : (∑ r ∈ T, weight r * (theta * redBase r)) +
      ∑ r ∈ T, weight r * ((1-theta)*cappedCost (redBase r) (redDistance r) X) =
      theta * (∑ r ∈ T, weight r * redBase r) +
      (1-theta) * (∑ r ∈ T, weight r * cappedCost (redBase r) (redDistance r) X) := by
    simp only [Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro r _ <;> ring
  simp only [mul_add, Finset.sum_add_distrib] at he ⊢
  rw [he]
  simp only [← Finset.mul_sum]
  nlinarith

lemma cappedCost_le_base {E : Type*} (b : ℝ) (d : E → ℝ) (X : Finset E) :
    cappedCost b d X ≤ b := (Finset.fold_min_le _).mpr (Or.inl le_rfl)

lemma cappedCost_le_offer {E : Type*} (b : ℝ) (d : E → ℝ) {X : Finset E} {e : E}
    (he : e ∈ X) : cappedCost b d X ≤ d e :=
  (Finset.fold_min_le _).mpr (Or.inr ⟨e, he, le_rfl⟩)

variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

lemma virtualNearest_le_real {a : ℕ} (H : Finset V) (w : Fin a → V)
    (radius : Fin a → ℝ) (M : ℝ) (x : V) {s : V} (hs : s ∈ H) :
    virtualNearest H w radius M x ≤ dist x s := by
  exact Finset.inf'_le _ (real_mem_withGhosts.mpr hs)

lemma virtualNearest_le_ball {a : ℕ} (H : Finset V) (w : Fin a → V)
    (radius : Fin a → ℝ) (M : ℝ) (x : V) (i : Fin a) :
    virtualNearest H w radius M x ≤ dist x (w i) + radius i := by
  exact Finset.inf'_le _ (ball_mem_withGhosts H i)

inductive Destination (V : Type*) (a : ℕ)
  | proxy : V → Destination V a
  | covered : Fin a → Destination V a
  | uncovered : V → Destination V a
  deriving DecidableEq

noncomputable def mixedDistance {a : ℕ} (theta : ℝ)
    (center w : Fin a → V) (radius : Fin a → ℝ) (s : V) : Destination V a → ℝ
  | .proxy φ => dist s φ
  | .covered i => theta * (dist s (w i) + radius i) + (1-theta)*dist s (center i)
  | .uncovered o => dist s o

omit [DecidableEq V] in

lemma mixedDistance_covered_triangle {a : ℕ} (theta : ℝ)
    (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) (center w : Fin a → V)
    (radius : Fin a → ℝ) (s p : V) (i : Fin a) :
    mixedDistance theta center w radius s (.covered i) ≤
      dist p s + dist p (center i) + theta * (dist (w i) (center i) + radius i) := by
  have h₀ := mul_le_mul_of_nonneg_left
    (dist_triangle s (center i) (w i)) ht0
  have h₁ := mul_le_mul_of_nonneg_left
    (dist_triangle s p (center i)) (show 0 ≤ 1-theta by linarith)
  have h₂ := mul_le_mul_of_nonneg_left
    (dist_triangle s p (center i)) ht0
  simp only [mixedDistance]
  rw [dist_comm (center i) (w i)] at h₀
  rw [dist_comm s p] at h₁ h₂
  nlinarith

lemma red_mixed_comparison {E : Type*} {a : ℕ} (G : Finset V)
    (loc : E → V) (X : Finset E) (center w : Fin a → V) (radius : Fin a → ℝ)
    (M theta : ℝ) (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1)
    (hcenter : ∀ i, ∃ e ∈ X, loc e = center i) (s : V)
    (d : Destination V a)
    (hd : match d with | .proxy φ => φ ∈ G | .covered _ => True | .uncovered _ => False) :
    theta * virtualNearest G w radius M s + (1-theta) *
      cappedCost (virtualNearest G w radius M s) (fun e => dist s (loc e)) X ≤
      mixedDistance theta center w radius s d := by
  have ht : 0 ≤ 1-theta := by linarith
  cases d with
  | proxy φ =>
    have hb := virtualNearest_le_real G w radius M s hd
    have hc := (cappedCost_le_base (virtualNearest G w radius M s) (fun e => dist s (loc e)) X).trans hb
    have h₀ := mul_le_mul_of_nonneg_left hb ht0
    have h₁ := mul_le_mul_of_nonneg_left hc ht
    simp only [mixedDistance]
    nlinarith
  | covered i =>
    obtain ⟨e, he, heloc⟩ := hcenter i
    have hb := virtualNearest_le_ball G w radius M s i
    have hc := cappedCost_le_offer (virtualNearest G w radius M s) (fun e => dist s (loc e)) he
    rw [heloc] at hc
    exact add_le_add (mul_le_mul_of_nonneg_left hb ht0) (mul_le_mul_of_nonneg_left hc ht)
  | uncovered o => exact hd.elim

omit [PseudoMetricSpace V] in
noncomputable def assignedClients {a : ℕ} (D T : Finset V) (assignment : V → Virtual V a) :
    Finset V := D.filter (fun p => ∃ s ∈ T, assignment p = Virtual.real s)

omit [PseudoMetricSpace V] in

lemma weighted_removal_bound {a : ℕ} (D T : Finset V)
    (assignment : V → Virtual V a) (mixed charge : V → ℝ)
    (hcharge : ∀ p ∈ D, ∀ s ∈ T, assignment p = Virtual.real s → mixed s ≤ charge p) :
    (∑ s ∈ T, assignmentWeight D assignment s * mixed s) ≤
      ∑ p ∈ assignedClients D T assignment, charge p := by
  classical
  have hs := sum_assignment_charges D assignment T id mixed
  simp only [id_eq] at hs
  rw [← hs, assignedClients, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro p hp
  by_cases hh : ∃ s ∈ T, assignment p = Virtual.real s
  · obtain ⟨s, hs, has⟩ := hh
    rw [ite_eq_left ⟨s, hs, has⟩]
    have he : (∑ r ∈ T, if assignment p = Virtual.real r then mixed r else 0) = mixed s := by
      rw [Finset.sum_eq_single s]
      · exact ite_eq_left has
      · intro r _ hrs
        apply ite_eq_right
        intro hr
        exact hrs (Virtual.real.inj (hr.symm.trans has))
      · exact fun hns => (hns hs).elim
    rw [he]
    exact hcharge p hp s hs has
  · rw [ite_eq_right hh]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro s hs
    exact ite_eq_right (fun he => hh ⟨s, hs, he⟩)

lemma interpolated_client_sum {P E : Type*} [DecidableEq P]
    (D J : Finset P) (hJ : J ⊆ D) (base : P → ℝ) (distance : P → E → ℝ)
    (X : Finset E) (theta : ℝ) (ht1 : theta ≤ 1) :
    (∑ p ∈ D, (theta*base p + (1-theta)*cappedCost (base p) (distance p) X : ℝ)) ≤
      (∑ p ∈ J, base p) +
      ∑ p ∈ D \ J, (theta*base p + (1-theta)*cappedCost (base p) (distance p) X : ℝ) := by
  rw [← Finset.sum_sdiff hJ (f := fun p => theta*base p +
    (1-theta)*cappedCost (base p) (distance p) X), add_comm]
  apply add_le_add _ le_rfl
  apply Finset.sum_le_sum
  intro p _
  have hh := mul_le_mul_of_nonneg_left (cappedCost_le_base (base p) (distance p) X)
    (show 0 ≤ 1-theta by linarith)
  nlinarith

end MetricKMedianRecovery.Completion

end OAI
