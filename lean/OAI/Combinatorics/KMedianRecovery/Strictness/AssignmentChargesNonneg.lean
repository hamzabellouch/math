import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.RealFilling

namespace OAI

namespace MetricKMedianRecovery.Completion
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

omit [PseudoMetricSpace V] in
lemma assignment_charges_nonneg {a : ℕ} {R : Type*} (T : Finset R)
    (assignment : V → Virtual V a) (loc : R → V) (charge : R → ℝ)
    (hc : ∀ r ∈ T, 0 ≤ charge r) (p : V) :
    0 ≤ ∑ r ∈ T, if assignment p = Virtual.real (loc r) then charge r else 0 := by
  apply Finset.sum_nonneg
  intro r hr
  split_ifs
  · exact hc r hr
  · rfl

omit [PseudoMetricSpace V] in
lemma assignment_charge_le {a : ℕ} {R : Type*} (T : Finset R)
    (assignment : V → Virtual V a) (loc : R → V) (charge : R → ℝ)
    (hc : ∀ r ∈ T, 0 ≤ charge r) (p : V) {r : R} (hr : r ∈ T)
    (hp : assignment p = Virtual.real (loc r)) :
    charge r ≤ ∑ s ∈ T, if assignment p = Virtual.real (loc s) then charge s else 0 := by
  have hh := Finset.single_le_sum (s := T) (f := fun s =>
    if assignment p = Virtual.real (loc s) then charge s else 0)
    (fun s hs => by split_ifs; exact hc s hs; rfl) hr
  simpa only [ite_eq_left hp] using hh

lemma realization_charging {E R B : Type*} {a : ℕ}
    (D F H G U : Finset V) (hU : U.Nonempty)
    (w : Fin a → V) (radius : Fin a → ℝ) (M : ℝ)
    (loc : E → V) (X : Finset E) (Tred : Finset R) (Tblue : Finset B)
    (redLoc : R → V) (blueLoc blueDest : B → V)
    (hr : ∀ i, 0 ≤ radius i) (hM0 : 0 ≤ M)
    (hUF : U ⊆ F) (hG : G ⊆ U)
    (hfill : ∀ i, ∃ u ∈ U, dist (w i) u ≤ radius i)
    (hM : ∀ x, ∀ f ∈ F, dist x f ≤ M) (hX : ∀ e ∈ X, loc e ∈ U)
    (hblue : ∀ b ∈ Tblue, blueDest b ∈ U)
    (hcover : ∀ s ∈ H, s ∈ U ∨ (∃ r ∈ Tred, redLoc r = s) ∨
      (∃ b ∈ Tblue, blueLoc b = s)) :
    (∑ p ∈ D, distanceTo U hU p) ≤
      (∑ p ∈ D, cappedCost (virtualNearest H w radius M p) (fun e => dist p (loc e)) X) +
      (∑ r ∈ Tred, assignmentWeight D (nearestTag H w radius M) (redLoc r) *
        cappedCost (virtualNearest G w radius M (redLoc r)) (fun e => dist (redLoc r) (loc e)) X) +
      ∑ b ∈ Tblue, assignmentWeight D (nearestTag H w radius M) (blueLoc b) *
        dist (blueLoc b) (blueDest b) := by
  let assignment := nearestTag H w radius M
  let redCost := fun r => cappedCost (virtualNearest G w radius M (redLoc r))
    (fun e => dist (redLoc r) (loc e)) X
  let blueCost := fun b => dist (blueLoc b) (blueDest b)
  let extraR := fun p => ∑ r ∈ Tred, if assignment p = Virtual.real (redLoc r) then redCost r else 0
  let extraB := fun p => ∑ b ∈ Tblue, if assignment p = Virtual.real (blueLoc b) then blueCost b else 0
  have hrednn : ∀ r ∈ Tred, 0 ≤ redCost r := by
    intro r _
    exact cappedCost_nonneg _ _ X (virtualNearest_nonneg G w radius M (redLoc r) hr hM0)
      (fun _ _ => dist_nonneg)
  have hbluenn : ∀ b ∈ Tblue, 0 ≤ blueCost b := fun _ _ => dist_nonneg
  have hRnn (p : V) : 0 ≤ extraR p := assignment_charges_nonneg Tred assignment redLoc redCost hrednn p
  have hBnn (p : V) : 0 ≤ extraB p := assignment_charges_nonneg Tblue assignment blueLoc blueCost hbluenn p
  have hbase (p : V) : distanceTo U hU p ≤ virtualNearest H w radius M p + extraR p + extraB p := by
    have ht := nearestTag_mem H w radius M p
    have hd := nearestTag_distance H w radius M p
    cases he : nearestTag H w radius M p with
    | real s =>
      rw [he,real_mem_withGhosts] at ht
      simp only [he,virtualDistance] at hd
      rcases hcover s ht with hs | ⟨r,hrm,rfl⟩ | ⟨b,hbm,rfl⟩
      · have hl := distanceTo_le hU p hs
        linarith [hRnn p,hBnn p]
      · have hl := nearest_le_redCost F U G hU w radius M loc X hUF hG hfill hM hX (redLoc r)
        have hex : redCost r ≤ extraR p :=
          assignment_charge_le Tred assignment redLoc redCost hrednn p hrm he
        have htri := distanceTo_triangle U hU p (redLoc r)
        linarith [hBnn p]
      · have hl := distanceTo_le hU (blueLoc b) (hblue b hbm)
        have hex : blueCost b ≤ extraB p :=
          assignment_charge_le Tblue assignment blueLoc blueCost hbluenn p hbm he
        have htri := distanceTo_triangle U hU p (blueLoc b)
        linarith [hRnn p]
    | ball i =>
      have hz := virtual_domination F U G hU w radius M hUF hG hfill hM p
        (Virtual.ball i) (ball_mem_withGhosts G i)
      rw [he] at hd
      linarith [hRnn p,hBnn p]
    | permanent =>
      have hz := virtual_domination F U G hU w radius M hUF hG hfill hM p
        Virtual.permanent (permanent_mem_withGhosts G)
      rw [he] at hd
      linarith [hRnn p,hBnn p]
  have hpoint (p : V) : distanceTo U hU p ≤
      cappedCost (virtualNearest H w radius M p) (fun e => dist p (loc e)) X + extraR p + extraB p := by
    have hh := le_cappedCost (virtualNearest H w radius M p) (fun e => dist p (loc e)) X
      (show distanceTo U hU p-extraR p-extraB p ≤ virtualNearest H w radius M p by linarith [hbase p])
      (fun e he => by have h := distanceTo_le hU p (hX e he); linarith [hRnn p,hBnn p])
    linarith
  have hsum := Finset.sum_le_sum (fun p (_ : p ∈ D) => hpoint p)
  simp only [Finset.sum_add_distrib] at hsum
  have hRsum := sum_assignment_charges D assignment Tred redLoc redCost
  have hBsum := sum_assignment_charges D assignment Tblue blueLoc blueCost
  change (∑ p ∈ D,extraR p) = _ at hRsum
  change (∑ p ∈ D,extraB p) = _ at hBsum
  rw [hRsum,hBsum] at hsum
  exact hsum

end MetricKMedianRecovery.Completion

end OAI
