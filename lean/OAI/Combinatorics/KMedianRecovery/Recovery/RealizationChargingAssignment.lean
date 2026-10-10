import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.RealCost

namespace OAI

namespace MetricKMedianRecovery.Completion
open Categorical FiniteSampling
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

lemma realization_charging_with_assignment {E R B : Type*} {a : ℕ}
    (D F H G U : Finset V) (hU : U.Nonempty)
    (w : Fin a → V) (radius : Fin a → ℝ) (M : ℝ)
    (assignment : V → Virtual V a)
    (hamem : ∀ p, assignment p ∈ withGhosts H)
    (hadist : ∀ p, virtualDistance w radius M p (assignment p) = virtualNearest H w radius M p)
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
      (∑ r ∈ Tred, assignmentWeight D assignment (redLoc r) *
        cappedCost (virtualNearest G w radius M (redLoc r)) (fun e => dist (redLoc r) (loc e)) X) +
      ∑ b ∈ Tblue, assignmentWeight D assignment (blueLoc b) *
        dist (blueLoc b) (blueDest b) := by
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
    have ht := hamem p
    have hd := hadist p
    cases he : assignment p with
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

lemma surrogate_realization_with_assignment {E R B : Type*} [DecidableEq E] [Fintype R] [Fintype B]
    [DecidableEq R] {a c q : ℕ}
    (D F S Q G : Finset V) (hS : S ⊆ F) (hn : S.Nonempty) (hQ : Q ⊆ S)
    (part : E → Fin a) (hp : Function.Surjective part) (loc : E → V)
    (w : Fin a → V) (radius : Fin a → ℝ) (M : ℝ)
    (assignment : V → Virtual V a)
    (hamem : ∀ p, assignment p ∈ withGhosts (S \ Q))
    (hadist : ∀ p, virtualDistance w radius M p (assignment p) = virtualNearest (S \ Q) w radius M p)
    (hr : ∀ i, 0 ≤ radius i) (hM0 : 0 ≤ M)
    (hloc : ∀ e, loc e ∈ F) (hball : ∀ e, dist (w (part e)) (loc e) ≤ radius (part e))
    (hM : ∀ x, ∀ f ∈ F, dist x f ≤ M)
    (redLoc : R → V) (blueLoc blueDest : B → V)
    (hredInj : Function.Injective redLoc) (hblueInj : Function.Injective blueLoc)
    (hred : ∀ r, redLoc r ∈ S \ Q) (hblue : ∀ b, blueLoc b ∈ S \ Q)
    (hRB : ∀ r b, redLoc r ≠ blueLoc b)
    (hG : G ⊆ S \ Q) (hGR : ∀ r, redLoc r ∉ G) (hGB : ∀ b, blueLoc b ∉ G)
    (hdest : ∀ b, blueDest b ∈ F) (hdestCount : (Finset.univ.image blueDest).card ≤ c)
    (hq : q ≤ Fintype.card R) (hcount : a+c ≤ Q.card+q+Fintype.card B)
    (K : ℝ)
    (hK : (∑ b, assignmentWeight D assignment (blueLoc b) *
      dist (blueLoc b) (blueDest b)) ≤ K)
    (X : Finset E) (hX : ∀ j, (X.filter (fun e => part e = j)).card ≤ 1) :
    ∃ U : Finset V, U ⊆ F ∧ U.card = S.card ∧ ∃ hU : U.Nonempty,
      (∑ p ∈ D, distanceTo U hU p) ≤
        K + (∑ p ∈ D, cappedCost (virtualNearest (S \ Q) w radius M p) (fun e => dist p (loc e)) X) +
        bottomSum q (fun r => assignmentWeight D assignment (redLoc r) *
          cappedCost (virtualNearest G w radius M (redLoc r)) (fun e => dist (redLoc r) (loc e)) X) := by
  classical
  let redCost := fun r => cappedCost (virtualNearest G w radius M (redLoc r))
    (fun e => dist (redLoc r) (loc e)) X
  obtain ⟨T, hT, heT⟩ := bottomSum_attained q
    (fun r => assignmentWeight D assignment (redLoc r) * redCost r)
  rw [min_eq_left hq] at hT
  let Red := T.image redLoc
  let Blue := Finset.univ.image blueLoc
  let Dest := Finset.univ.image blueDest
  have hRcard : Red.card = q := by rw [Finset.card_image_of_injective _ hredInj,hT]
  have hBcard : Blue.card = Fintype.card B := by simp [Blue,Finset.card_image_of_injective _ hblueInj]
  have hRsub : Red ⊆ S \ Q := by
    intro s hs
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hs
    exact hred r
  have hBsub : Blue ⊆ S \ Q := by
    intro s hs
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hs
    exact hblue b
  have hRBD : Disjoint Red Blue := by
    apply Finset.disjoint_left.mpr
    intro s hs hs'
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨b,_,he⟩ := Finset.mem_image.mp hs'
    exact hRB r b he.symm
  obtain ⟨Filled,hFF,hFc,hFX,hFi⟩ := exists_real_filling F part hp loc w radius hloc hball X hX
  have hDF : Dest ⊆ F := by
    intro x hx
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hx
    exact hdest b
  have hAddc : (Filled ∪ Dest).card ≤ Q.card + Red.card + Blue.card := by
    have hd : Dest.card ≤ c := hdestCount
    have hh := Finset.card_union_le Filled Dest
    rw [hRcard,hBcard]
    omega
  obtain ⟨U,hUF,hUc,hUn,hU₀⟩ := padded_completion F S Q Red Blue (Filled ∪ Dest)
    hS hn hQ hRsub hBsub hRBD (Finset.union_subset hFF hDF) hAddc
  have hFU : Filled ⊆ U := by
    intro f hf
    exact hU₀ (Finset.mem_union_right _ (Finset.mem_union_left _ hf))
  have hDU : Dest ⊆ U := by
    intro d hd
    exact hU₀ (Finset.mem_union_right _ (Finset.mem_union_right _ hd))
  have hGU : G ⊆ U := by
    intro s hs
    apply hU₀
    apply Finset.mem_union_left
    apply Finset.mem_sdiff.mpr
    refine ⟨(Finset.mem_sdiff.mp (hG hs)).1,?_⟩
    intro hb
    rcases Finset.mem_union.mp hb with hb | hb
    · rcases Finset.mem_union.mp hb with hb | hb
      · exact (Finset.mem_sdiff.mp (hG hs)).2 hb
      · obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hb
        exact hGR r hs
    · obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hb
      exact hGB b hs
  have hFillU : ∀ i, ∃ u ∈ U, dist (w i) u ≤ radius i := by
    intro i
    obtain ⟨u,hu,hb⟩ := hFi i
    exact ⟨u,hFU hu,hb⟩
  have hXU : ∀ e ∈ X, loc e ∈ U := fun e he => hFU (hFX e he)
  have hBlueU : ∀ b ∈ (Finset.univ : Finset B), blueDest b ∈ U := by
    intro b _
    exact hDU (Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩)
  have hcover : ∀ s ∈ S \ Q, s ∈ U ∨ (∃ r ∈ T, redLoc r = s) ∨
      (∃ b ∈ (Finset.univ : Finset B), blueLoc b = s) := by
    intro s hs
    by_cases hR : s ∈ Red
    · exact Or.inr (Or.inl (Finset.mem_image.mp hR))
    by_cases hB : s ∈ Blue
    · exact Or.inr (Or.inr (Finset.mem_image.mp hB))
    apply Or.inl
    apply hU₀
    apply Finset.mem_union_left
    apply Finset.mem_sdiff.mpr
    refine ⟨(Finset.mem_sdiff.mp hs).1,?_⟩
    simp only [Finset.mem_union,not_or]
    exact ⟨⟨(Finset.mem_sdiff.mp hs).2,hR⟩,hB⟩
  have hh := realization_charging_with_assignment D F (S \ Q) G U hUn w radius M assignment hamem hadist loc X T Finset.univ
    redLoc blueLoc blueDest hr hM0 hUF hGU hFillU hM hXU hBlueU hcover
  refine ⟨U,hUF,hUc,hUn,?_⟩
  change (∑ r ∈ T,assignmentWeight D assignment (redLoc r) *
    cappedCost (virtualNearest G w radius M (redLoc r)) (fun e => dist (redLoc r) (loc e)) X) = _ at heT
  rw [heT] at hh
  linarith

lemma sampled_metric_branch_with_assignment {E R B : Type*} [Fintype E] [DecidableEq E]
    [Fintype R] [Fintype B] [DecidableEq R] {a c q : ℕ}
    (D F S Q G : Finset V) (hS : S ⊆ F) (hn : S.Nonempty) (hQ : Q ⊆ S)
    (part : E → Fin a) (hp : Function.Surjective part) (loc : E → V)
    (w : Fin a → V) (radius : Fin a → ℝ) (M : ℝ)
    (assignment : V → Virtual V a)
    (hamem : ∀ p, assignment p ∈ withGhosts (S \ Q))
    (hadist : ∀ p, virtualDistance w radius M p (assignment p) = virtualNearest (S \ Q) w radius M p)
    (hr : ∀ i, 0 ≤ radius i) (hM0 : 0 ≤ M)
    (hloc : ∀ e, loc e ∈ F) (hball : ∀ e, dist (w (part e)) (loc e) ≤ radius (part e))
    (hM : ∀ x, ∀ f ∈ F, dist x f ≤ M)
    (redLoc : R → V) (blueLoc blueDest : B → V)
    (hredInj : Function.Injective redLoc) (hblueInj : Function.Injective blueLoc)
    (hred : ∀ r, redLoc r ∈ S \ Q) (hblue : ∀ b, blueLoc b ∈ S \ Q)
    (hRB : ∀ r b, redLoc r ≠ blueLoc b)
    (hG : G ⊆ S \ Q) (hGR : ∀ r, redLoc r ∉ G) (hGB : ∀ b, blueLoc b ∉ G)
    (hdest : ∀ b, blueDest b ∈ F) (hdestCount : (Finset.univ.image blueDest).card ≤ c)
    (hq : q ≤ Fintype.card R) (hcount : a+c ≤ Q.card+q+Fintype.card B)
    (K : ℝ)
    (hK : (∑ b, assignmentWeight D assignment (blueLoc b) *
      dist (blueLoc b) (blueDest b)) ≤ K)
    (theta : ℝ) (htheta : 1/Real.exp 1 < theta) :
    let Ψ := surrogate (P := ↥D) K q
      (fun p => virtualNearest (S \ Q) w radius M p)
      (fun p e => dist (p : V) (loc e))
      (fun r => assignmentWeight D assignment (redLoc r))
      (fun r => virtualNearest G w radius M (redLoc r))
      (fun r e => dist (redLoc r) (loc e))
    ∃ out : (BinaryOracleIndex E a (stepExponent a (theta-1/Real.exp 1))
        (sampleCount (Fintype.card E) a (theta-1/Real.exp 1)) → Bool) → Finset V,
      (∀ bits, out bits ⊆ F ∧ (out bits).card = S.card ∧ (out bits).Nonempty) ∧
      ∀ X, PartitionFeasible part X →
        average (fun bits => realCost D (out bits)) ≤ theta * Ψ ∅ + (1-theta) * Ψ X := by
  classical
  dsimp only
  let base : ↥D → ℝ := fun p => virtualNearest (S \ Q) w radius M p
  let distance : ↥D → E → ℝ := fun p e => dist (p : V) (loc e)
  let weight : R → ℝ := fun r => assignmentWeight D assignment (redLoc r)
  let redBase : R → ℝ := fun r => virtualNearest G w radius M (redLoc r)
  let redDistance : R → E → ℝ := fun r e => dist (redLoc r) (loc e)
  let choice := sampledSurrogate part hp K q base distance weight redBase redDistance
    (theta-1/Real.exp 1)
  have hreal : ∀ bits, ∃ U : Finset V, U ⊆ F ∧ U.card = S.card ∧ U.Nonempty ∧
      realCost D U ≤ surrogate K q base distance weight redBase redDistance (choice bits) := by
    intro bits
    obtain ⟨U, hUF, hUc, hUn, hcost⟩ := surrogate_realization_with_assignment
      D F S Q G hS hn hQ part hp loc w radius M assignment hamem hadist hr hM0 hloc hball hM
      redLoc blueLoc blueDest hredInj hblueInj hred hblue hRB hG hGR hGB hdest hdestCount
      hq hcount K hK (choice bits) (sampledSurrogate_feasible part hp K q base distance
        weight redBase redDistance (theta-1/Real.exp 1) bits)
    refine ⟨U, hUF, hUc, hUn, ?_⟩
    simp only [realCost, dite_eq_left hUn]
    change (∑ p ∈ D, distanceTo U hUn p) ≤
      K + (∑ p : ↥D, cappedCost (virtualNearest (S \ Q) w radius M p)
        (fun e => dist (p : V) (loc e)) (choice bits)) + _
    rw [Finset.sum_coe_sort D (fun p => cappedCost (virtualNearest (S \ Q) w radius M p)
      (fun e => dist p (loc e)) (choice bits))]
    exact hcost
  choose out hout using hreal
  refine ⟨out, fun bits => ⟨(hout bits).1, (hout bits).2.1, (hout bits).2.2.1⟩, ?_⟩
  intro X hX
  refine (average_mono (fun bits => (hout bits).2.2.2)).trans ?_
  exact sampledSurrogate_expected part hp K q base distance weight redBase redDistance
    (fun r => assignmentWeight_nonneg _ _ _) htheta X hX

end MetricKMedianRecovery.Completion

end OAI
