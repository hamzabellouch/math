import OAI.Combinatorics.EditApproximation.Geometry.ChargedGlobalQuery
import OAI.Combinatorics.EditApproximation.Geometry.RefinementSupportBudget

namespace OAI

/-! Literal seed, initial-cone and warmup query counts. No accuracy event
is needed: even rejected local centers are included in these bounds. -/

namespace EditApproximation

theorem rawInitialConeCenters_length {n : ℕ} (N P Amax : ℕ) (A : ℚ)
    (value : ℕ) (q : TargetInterval n) (hP : 0 < P) (hA : 1 ≤ A) (hmax : A ≤ Amax) :
    (rawInitialConeCenters N P A value q).length ≤
      (dyadicScales N).length * (64 * Amax ^ 2 * P + 2) ^ 2 := by
  unfold rawInitialConeCenters
  apply (list_flatMap_length_le _ _ _ ?_).trans
    (Nat.mul_le_mul_right _ (List.length_filter_le _ _))
  intro b hb
  have hwindow := of_decide_eq_true (List.mem_filter.mp hb).2
  have hApos : 0 < A := by linarith
  have hscale : (value : ℚ) ≤ 16 * A ^ 2 * b := by
    have h := (div_le_iff₀ (by positivity : (0 : ℚ) < 16 * A ^ 2)).mp hwindow.1
    nlinarith only [h]
  have hAsq : A ^ 2 ≤ (Amax : ℚ) ^ 2 := pow_le_pow_left₀ hApos.le hmax 2
  have hradius : value ≤ 16 * Amax ^ 2 * b := by
    have hmul := mul_le_mul_of_nonneg_right hAsq (by positivity : (0 : ℚ) ≤ 16 * b)
    have h : (value : ℚ) ≤ (16 * Amax ^ 2 * b : ℕ) := by
      push_cast
      nlinarith only [hscale, hmul]
    exact_mod_cast h
  simpa only [show 4 * (16 * Amax ^ 2) * P = 64 * Amax ^ 2 * P by ring] using
    localTargetStates_length_from_scale P b value (16 * Amax ^ 2) q hP hradius

theorem physicalInitialQuery_cost_le {ι α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (N P F Amax seedCost : ℕ) (A : ℚ)
    (seedRead : PhysicalEntry M J target.length → FiniteQuery ι)
    (node : PhysicalNode M J) (q : TargetInterval target.length) (oracle : ι → ℚ)
    (hP : 0 < P) (hA : 1 ≤ A) (hmax : A ≤ Amax)
    (hseed : ∀ r, (seedRead (node, r)).cost oracle (fun _ => 1) ≤ seedCost) :
    (physicalInitialQuery source target N P F A seedRead (node, q)).cost oracle (fun _ => 1) ≤
      (1 + (dyadicScales N).length * (64 * Amax ^ 2 * P + 2) ^ 2) * seedCost := by
  unfold physicalInitialQuery
  dsimp only
  split_ifs
  · exact Nat.zero_le _
  · rw [FiniteQuery.cost_bind]
    have hkeys := rawInitialConeCenters_length N P Amax A
      ⌈(seedRead (node, q)).value oracle⌉₊ q hP hA hmax
    rw [FiniteQuery.cost_collect]
    simp only [FiniteQuery.cost, Nat.add_zero]
    have hc := list_map_sum_le_constant
      (rawInitialConeCenters N P A ⌈(seedRead (node, q)).value oracle⌉₊ q)
      (fun r => (seedRead (node, r)).cost oracle (fun _ => 1)) seedCost
      (fun r => hseed r)
    calc
      _ ≤ seedCost + (rawInitialConeCenters N P A
          ⌈(seedRead (node, q)).value oracle⌉₊ q).length * seedCost :=
        Nat.add_le_add (hseed q) hc
      _ ≤ seedCost + ((dyadicScales N).length * (64 * Amax ^ 2 * P + 2) ^ 2) * seedCost := by
        simpa only [Nat.add_zero] using Nat.add_le_add_left (Nat.mul_le_mul_right seedCost hkeys) seedCost
      _ = _ := by ring

theorem localWarmupStepQuery_cost_le {ι : Type*} {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F window initialCost childCost : ℕ) (a : ℚ)
    (initialRead : TargetInterval ny → FiniteQuery ι)
    (childRead : Fin M × TargetInterval ny → FiniteQuery ι)
    (oracle : ι → ℚ) (q : TargetInterval ny) (hP : 0 < P) (hF : 1 ≤ F)
    (hwindow : ∀ w, (dyadicQueryWindow N w a F).length ≤ window)
    (hinitial : ∀ r, (initialRead r).cost oracle (fun _ => 1) ≤ initialCost)
    (hchild : ∀ input, (childRead input).cost oracle (fun _ => 1) ≤ childCost) :
    (localWarmupStepQuery parent N P F a initialRead childRead q).cost oracle (fun _ => 1) ≤
      (1 + window * (64 * F * P + 2) ^ 2) * initialCost +
        window * (64 * F * P + 2) ^ 2 * M * (40 * P + 2) ^ 2 * childCost := by
  let value := (initialRead q).value oracle
  let centers := rawRefinementCenters N P F a value q
  have hcenters : centers.length ≤ window * (64 * F * P + 2) ^ 2 :=
    (rawRefinementCenters_length N P F a value q hP hF).trans
      (Nat.mul_le_mul_right _ (hwindow value))
  have hnext (answers : List ℚ) :
      (FiniteQuery.collect childRead
        (wideWarmupInputs (M := M) parent P
          (localRefinementRepresentatives N P F a
            (fun r => if r = q then value else finiteAnswerTable centers answers r) q))
        (fun values => .done (rationalBellman (M := M)
          (fun r => if r = q then value else finiteAnswerTable centers answers r)
          (fun q r => targetEndpointDistance q r) (128 * F)
          (rationalActualWideActions parent
            (localRefinementRepresentatives N P F a
              (fun r => if r = q then value else finiteAnswerTable centers answers r) q) P)
          (finiteAnswerTable (wideWarmupInputs (M := M) parent P
            (localRefinementRepresentatives N P F a
              (fun r => if r = q then value else finiteAnswerTable centers answers r) q)) values) q))).cost oracle (fun _ => 1) ≤
        window * (64 * F * P + 2) ^ 2 * M * (40 * P + 2) ^ 2 * childCost := by
    have hreps := localRefinementRepresentatives_length N P F a
      (fun r => if r = q then value else finiteAnswerTable centers answers r) q hP hF
    have hlen := (wideWarmupInputs_length (M := M) parent P _ hP).trans
      (Nat.mul_le_mul_right ((40 * P + 2) ^ 2) (Nat.mul_le_mul_right M
        (hreps.trans (Nat.mul_le_mul_right _ (hwindow _)))))
    rw [FiniteQuery.cost_collect]
    simp only [FiniteQuery.cost, Nat.add_zero]
    exact (list_map_sum_le_constant _ (fun input => (childRead input).cost oracle (fun _ => 1))
      childCost (fun input => hchild input)).trans (Nat.mul_le_mul_right childCost hlen)
  unfold localWarmupStepQuery
  rw [FiniteQuery.cost_bind]
  rw [FiniteQuery.cost_collect]
  have hc := Nat.add_le_add
    (list_map_sum_le_constant centers (fun r => (initialRead r).cost oracle (fun _ => 1)) initialCost hinitial)
    (hnext (centers.map fun r => (initialRead r).value oracle))
  calc
    _ ≤ initialCost + (centers.length * initialCost +
        window * (64 * F * P + 2) ^ 2 * M * (40 * P + 2) ^ 2 * childCost) :=
      Nat.add_le_add (hinitial q) hc
    _ ≤ initialCost + (window * (64 * F * P + 2) ^ 2 * initialCost +
        window * (64 * F * P + 2) ^ 2 * M * (40 * P + 2) ^ 2 * childCost) :=
      Nat.add_le_add_left (Nat.add_le_add_right (Nat.mul_le_mul_right initialCost hcenters) _) _
    _ = _ := by ring

theorem chargedSeedQuery_cost_le {M J ny passes copies T S : ℕ} (N : ℕ) (multiplier : ℕ → ℕ)
    (parent : {r : PhysicalTableRequest M J ny // r.Bounded passes copies T S})
    (state : PhysicalEntry M J ny) (oracle) :
    (chargedSeedQuery N multiplier parent state).cost oracle (fun _ => 1) ≤ max 1 copies := by
  rw [chargedSeedQuery_cost]
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _
  · exact Nat.zero_le _

theorem chargedWarmupQuery_cost_le {α : Type*} [DecidableEq α] {M J passes copies T S : ℕ}
    (source target : List α) (N P F Amax window : ℕ)
    (factor : ℕ → ℚ) (multiplier : ℕ → ℕ)
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
    (oracle) (hP : 0 < P) (hF : 1 ≤ F) (hA : 1 ≤ factor parent.val.pass)
    (hmax : factor parent.val.pass ≤ Amax)
    (hwindow : ∀ w, (dyadicQueryWindow N w (refinementFactor (factor parent.val.pass) F) F).length ≤ window) :
    (chargedWarmupQuery source target N P F factor multiplier parent).cost oracle (fun _ => 1) ≤
      (1 + window * (64 * F * P + 2) ^ 2) *
        ((1 + (dyadicScales N).length * (64 * Amax ^ 2 * P + 2) ^ 2) * max 1 copies) +
        window * (64 * F * P + 2) ^ 2 * M * (40 * P + 2) ^ 2 := by
  let initialCost := (1 + (dyadicScales N).length * (64 * Amax ^ 2 * P + 2) ^ 2) * max 1 copies
  have hinitial (r : TargetInterval target.length) :
      (physicalInitialQuery source target N P F (factor parent.val.pass)
        (chargedSeedQuery N multiplier parent) (parent.val.node, r)).cost oracle (fun _ => 1) ≤ initialCost :=
    physicalInitialQuery_cost_le source target N P F Amax (max 1 copies) _ _ _ r oracle hP hA hmax
      (fun s => chargedSeedQuery_cost_le N multiplier parent _ oracle)
  have hinitialBound : initialCost ≤
      (1 + window * (64 * F * P + 2) ^ 2) * initialCost +
        window * (64 * F * P + 2) ^ 2 * M * (40 * P + 2) ^ 2 := by
    exact (Nat.le_mul_of_pos_left initialCost (by omega)).trans (Nat.le_add_right _ _)
  unfold chargedWarmupQuery
  split_ifs with hz hbelow hshort
  · exact (hinitial _).trans hinitialBound
  · exact (hinitial _).trans hinitialBound
  · unfold physicalWarmupStepQuery
    simpa only [Nat.mul_one] using localWarmupStepQuery_cost_le
      (physicalSourceInterval source.length parent.val.node) N P F window initialCost 1
      (refinementFactor (factor parent.val.pass) F) _ _ oracle parent.val.state hP hF hwindow hinitial
      (fun input => by simp only [chargedWarmupChild, FiniteQuery.cost, Nat.add_zero, le_refl])
  · exact (hinitial _).trans hinitialBound

end EditApproximation

end OAI
