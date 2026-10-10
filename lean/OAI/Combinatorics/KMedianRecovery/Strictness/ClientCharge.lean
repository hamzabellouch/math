import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Destination

namespace OAI

namespace MetricKMedianRecovery.Completion
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

noncomputable def clientCharge {a : ℕ} (theta : ℝ) (center w : Fin a → V)
    (radius : Fin a → ℝ) (p : V) : Destination V a → ℝ
  | .proxy φ => dist p φ
  | .covered i => dist p (center i) + theta * (dist (w i) (center i) + radius i)
  | .uncovered i => dist p i

noncomputable def minimumMixed {a : ℕ} (theta : ℝ) (center w : Fin a → V)
    (radius : Fin a → ℝ) (Ω : Finset (Destination V a)) (hΩ : Ω.Nonempty) (s : V) : ℝ :=
  Ω.inf' hΩ (mixedDistance theta center w radius s)

noncomputable def selectedDestination {a : ℕ} (theta : ℝ) (center w : Fin a → V)
    (radius : Fin a → ℝ) (Ω : Finset (Destination V a)) (hΩ : Ω.Nonempty) (s : V) : Destination V a :=
  Classical.choose (Finset.exists_min_image Ω (mixedDistance theta center w radius s) hΩ)

omit [DecidableEq V] in
lemma selectedDestination_mem {a : ℕ} (theta : ℝ) (center w : Fin a → V)
    (radius : Fin a → ℝ) (Ω : Finset (Destination V a)) (hΩ : Ω.Nonempty) (s : V) :
    selectedDestination theta center w radius Ω hΩ s ∈ Ω :=
  (Classical.choose_spec (Finset.exists_min_image Ω (mixedDistance theta center w radius s) hΩ)).1

omit [DecidableEq V] in
lemma selectedDestination_distance {a : ℕ} (theta : ℝ) (center w : Fin a → V)
    (radius : Fin a → ℝ) (Ω : Finset (Destination V a)) (hΩ : Ω.Nonempty) (s : V) :
    mixedDistance theta center w radius s (selectedDestination theta center w radius Ω hΩ s) =
      minimumMixed theta center w radius Ω hΩ s := by
  apply le_antisymm
  · exact Finset.le_inf' _ _ (fun d hd =>
      (Classical.choose_spec (Finset.exists_min_image Ω (mixedDistance theta center w radius s) hΩ)).2 d hd)
  · exact Finset.inf'_le _ (selectedDestination_mem theta center w radius Ω hΩ s)

omit [DecidableEq V] in
lemma mixedDistance_client_triangle {a : ℕ} (theta : ℝ)
    (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) (center w : Fin a → V) (radius : Fin a → ℝ)
    (s p : V) (d : Destination V a) :
    mixedDistance theta center w radius s d ≤ dist p s + clientCharge theta center w radius p d := by
  cases d with
  | proxy φ => simpa only [mixedDistance,clientCharge,dist_comm s p] using dist_triangle s p φ
  | covered i => simpa only [clientCharge,add_assoc] using mixedDistance_covered_triangle theta ht0 ht1 center w radius s p i
  | uncovered i => simpa only [mixedDistance,clientCharge,dist_comm s p] using dist_triangle s p i

lemma removal_comparison_charge {a : ℕ} (D H Rstar : Finset V)
    (w center : Fin a → V) (radius : Fin a → ℝ) (M theta : ℝ)
    (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1)
    (assignment : V → Virtual V a)
    (hadist : ∀ p, virtualDistance w radius M p (assignment p) = virtualNearest H w radius M p)
    (Ω : Finset (Destination V a)) (hΩ : Ω.Nonempty) (own : V → Destination V a)
    (hown : ∀ p ∈ D, own p ∈ Ω) :
    (∑ s ∈ Rstar, assignmentWeight D assignment s * minimumMixed theta center w radius Ω hΩ s) ≤
      (∑ p ∈ assignedClients D Rstar assignment, virtualNearest H w radius M p) +
      ∑ p ∈ assignedClients D Rstar assignment, clientCharge theta center w radius p (own p) := by
  rw [← Finset.sum_add_distrib]
  apply weighted_removal_bound
  intro p hp s _ has
  have hh := (Finset.inf'_le (mixedDistance theta center w radius s) (hown p hp)).trans
    (mixedDistance_client_triangle theta ht0 ht1 center w radius s p (own p))
  have hd := hadist p
  simp only [has,virtualDistance] at hd
  change minimumMixed theta center w radius Ω hΩ s ≤ virtualNearest H w radius M p + _
  rw [← hd]
  exact hh

lemma surrogate_comparison_bound {E R : Type*} [DecidableEq E] [Fintype R]
    {a q : ℕ} (D H G Rstar Blue : Finset V)
    (w center : Fin a → V) (radius : Fin a → ℝ) (M theta K : ℝ)
    (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1)
    (assignment : V → Virtual V a) (redLoc : R → V) (hredInj : Function.Injective redLoc)
    (T : Finset R) (hT : T.card = q)
    (hdisj : Disjoint (T.image redLoc) Blue) (hcover : T.image redLoc ∪ Blue = Rstar)
    (loc : E → V) (X : Finset E) (hcenter : ∀ i, ∃ e ∈ X, loc e = center i)
    (Ω : Finset (Destination V a)) (hΩ : Ω.Nonempty)
    (hredDest : ∀ r ∈ T,
      match selectedDestination theta center w radius Ω hΩ (redLoc r) with
      | .proxy φ => φ ∈ G | .covered _ => True | .uncovered _ => False)
    (hK : K ≤ ∑ s ∈ Blue, assignmentWeight D assignment s * minimumMixed theta center w radius Ω hΩ s) :
    let Ψ := surrogate (P := ↥D) K q
      (fun p => virtualNearest H w radius M p) (fun p e => dist (p:V) (loc e))
      (fun r => assignmentWeight D assignment (redLoc r))
      (fun r => virtualNearest G w radius M (redLoc r)) (fun r e => dist (redLoc r) (loc e))
    theta * Ψ ∅ + (1-theta) * Ψ X ≤
      (∑ p ∈ D, (theta * virtualNearest H w radius M p + (1-theta) *
        cappedCost (virtualNearest H w radius M p) (fun e => dist p (loc e)) X)) +
      ∑ s ∈ Rstar, assignmentWeight D assignment s * minimumMixed theta center w radius Ω hΩ s := by
  dsimp only
  have hh := convex_surrogate_upper K q
    (fun p : ↥D => virtualNearest H w radius M p) (fun p e => dist (p:V) (loc e))
    (fun r => assignmentWeight D assignment (redLoc r))
    (fun r => virtualNearest G w radius M (redLoc r)) (fun r e => dist (redLoc r) (loc e))
    theta ht0 ht1 T hT X
  rw [Finset.sum_coe_sort D (fun p => theta * virtualNearest H w radius M p + (1-theta) *
    cappedCost (virtualNearest H w radius M p) (fun e => dist p (loc e)) X)] at hh
  refine hh.trans ?_
  have hred : (∑ r ∈ T, assignmentWeight D assignment (redLoc r) *
      (theta * virtualNearest G w radius M (redLoc r) + (1-theta) *
        cappedCost (virtualNearest G w radius M (redLoc r)) (fun e => dist (redLoc r) (loc e)) X)) ≤
      ∑ s ∈ T.image redLoc, assignmentWeight D assignment s * minimumMixed theta center w radius Ω hΩ s := by
    rw [Finset.sum_image (fun r _ r' _ he => hredInj he)]
    apply Finset.sum_le_sum
    intro r hr
    apply mul_le_mul_of_nonneg_left _ (assignmentWeight_nonneg _ _ _)
    have hrule := red_mixed_comparison G loc X center w radius M theta ht0 ht1 hcenter (redLoc r)
      (selectedDestination theta center w radius Ω hΩ (redLoc r)) (hredDest r hr)
    rwa [selectedDestination_distance] at hrule
  rw [← hcover,Finset.sum_union hdisj]
  linarith

lemma completion_endpoint_bound {E : Type*} {a : ℕ} (D H Rstar : Finset V)
    (w center : Fin a → V) (radius : Fin a → ℝ) (M theta : ℝ)
    (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) (assignment : V → Virtual V a)
    (hadist : ∀ p, virtualDistance w radius M p (assignment p) = virtualNearest H w radius M p)
    (Ω : Finset (Destination V a)) (hΩ : Ω.Nonempty) (own : V → Destination V a)
    (hown : ∀ p ∈ D, own p ∈ Ω) (loc : E → V) (X : Finset E) :
    (∑ p ∈ D, (theta * virtualNearest H w radius M p + (1-theta) *
      cappedCost (virtualNearest H w radius M p) (fun e => dist p (loc e)) X)) +
      (∑ s ∈ Rstar, assignmentWeight D assignment s * minimumMixed theta center w radius Ω hΩ s) ≤
    2 * (∑ p ∈ assignedClients D Rstar assignment, virtualNearest H w radius M p) +
      (∑ p ∈ assignedClients D Rstar assignment, clientCharge theta center w radius p (own p)) +
      ∑ p ∈ D \ assignedClients D Rstar assignment,
        (theta * virtualNearest H w radius M p + (1-theta) *
          cappedCost (virtualNearest H w radius M p) (fun e => dist p (loc e)) X) := by
  have hb := interpolated_client_sum D (assignedClients D Rstar assignment)
    (Finset.filter_subset _ _) (virtualNearest H w radius M) (fun p e => dist p (loc e)) X theta ht1
  have hr := removal_comparison_charge D H Rstar w center radius M theta ht0 ht1 assignment hadist Ω hΩ own hown
  linarith

end MetricKMedianRecovery.Completion

end OAI
