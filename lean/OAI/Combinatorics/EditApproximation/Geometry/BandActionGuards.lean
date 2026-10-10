import OAI.Combinatorics.EditApproximation.Geometry.BandRounding
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Actual rounded band actions pass the finite guards

Each child uses its own envelope-derived integer spacing. The action is
rounded with literal integer division; wide-grid, radius and imbalance
claims are proved for these returned states.
-/

namespace EditApproximation

open Finset





theorem bandChildEnvelope_pos {ny M : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → ℚ) (i : Fin M) :
    0 < bandChildEnvelope b band initial i := by
  unfold bandChildEnvelope rationalDyadicCeiling
  positivity

theorem roundedBandAction_endpoint_error {ny M : ℕ} (thetaExponent b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → ℚ) (action : Fin M → TargetInterval ny) (i : Fin M) :
    (Nat.dist (action i).lo (roundedBandAction thetaExponent b band initial action i).lo : ℚ) ≤
        (2 : ℚ) ^ (-(thetaExponent : ℤ)) * bandChildEnvelope b band initial i ∧
      (Nat.dist (action i).hi (roundedBandAction thetaExponent b band initial action i).hi : ℚ) ≤
        (2 : ℚ) ^ (-(thetaExponent : ℤ)) * bandChildEnvelope b band initial i := by
  have hscaled : 0 ≤ (2 : ℚ) ^ (-(thetaExponent : ℤ)) * bandChildEnvelope b band initial i :=
    mul_nonneg (zpow_pos (by norm_num : (0 : ℚ) < 2) _).le (bandChildEnvelope_pos b band initial i).le
  exact ⟨gridRound_scaled_error _ _ _ (bandRoundSpacing_exact thetaExponent b band initial i) hscaled,
    gridRound_scaled_error _ _ _ (bandRoundSpacing_exact thetaExponent b band initial i) hscaled⟩

theorem roundedBandAction_distance {ny M : ℕ} (thetaExponent b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → ℚ) (action : Fin M → TargetInterval ny) (i : Fin M) :
    (targetEndpointDistance (action i) (roundedBandAction thetaExponent b band initial action i) : ℚ) ≤
      2 * (2 : ℚ) ^ (-(thetaExponent : ℤ)) * bandChildEnvelope b band initial i := by
  have h := roundedBandAction_endpoint_error thetaExponent b band initial action i
  unfold targetEndpointDistance
  push_cast
  convert add_le_add h.1 h.2 using 1
  ring

/-- Actual rounded wide membership and imbalance guard. The sum premise
is supplied by bandChildEnvelope_sum_guard, and the remaining premises
are explicit computed-parameter inequalities. -/
theorem roundedBandAction_guards {α : Type*} (source target : List α)
    {M b P : ℕ} (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (thetaExponent : ℕ) (tau velocity : ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (action : Fin M → TargetInterval target.length)
    (haction : action ∈ computedBandActions parent r b P tau ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child)
    (hM : 0 < M) (hPpos : 0 < P)
    (hbPower : ∃ e : ℕ, b = 2 ^ e) (hPPower : ∃ e : ℕ, P = 2 ^ e)
    (hscale : (M : ℚ) ≤ (2 : ℚ) ^ (-(thetaExponent : ℤ)) * P)
    (F : ℚ)
    (hsmall : 64 * F * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ 4)
    (htheta : (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ 1 / 2)
    (hinitialGap : ∀ i s, |rationalStateGap
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s| ≤ initial i s)
    (hsum : (∑ i : Fin M, bandChildEnvelope b
      (computedBandActions parent r b P tau ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child) initial i) ≤ 64 * F * b) :
    let band := computedBandActions parent r b P tau ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child
    roundedBandAction thetaExponent b band initial action ∈ wideActionList M parent r b P ∧
      ∀ i, |rationalStateGap
        (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target
          (roundedBandAction thetaExponent b band initial action i)| ≤ 2 * bandChildEnvelope b band initial i := by
  let theta : ℚ := 2 ^ (-(thetaExponent : ℤ))
  let band := computedBandActions parent r b P tau theta velocity child
  let envelope := fun i : Fin M => bandChildEnvelope b band initial i
  let rounded := roundedBandAction thetaExponent b band initial action
  have htheta0 : 0 ≤ theta := (zpow_pos (by norm_num : (0 : ℚ) < 2) _).le
  have henv (i : Fin M) : 0 ≤ envelope i := (bandChildEnvelope_pos b band initial i).le
  have hsingle (i : Fin M) : envelope i ≤ ∑ j, envelope j :=
    single_le_sum (fun j _ => henv j) (mem_univ i)
  have hbudget (i : Fin M) : theta * envelope i ≤ 4 * b := by
    have h := (mul_le_mul_of_nonneg_left (hsingle i) htheta0).trans
      (mul_le_mul_of_nonneg_left hsum htheta0)
    have hb := mul_le_mul_of_nonneg_right hsmall (show (0 : ℚ) ≤ b by positivity)
    nlinarith only [h, hb]
  obtain ⟨hnonempty, hwide, hv, hpredicate⟩ :=
    computedBandActions_mem parent r b P tau theta velocity child action haction
  have herr := roundedBandAction_endpoint_error thetaExponent b band initial action
  have hanchor (anchor before after : ℕ) (i : Fin M)
      (hbefore : Nat.dist anchor before ≤ 6 * b)
      (herror : (Nat.dist before after : ℚ) ≤ theta * envelope i) :
      Nat.dist anchor after ≤ 10 * b := by
    have htriangle : (Nat.dist anchor after : ℚ) ≤ (Nat.dist anchor before : ℚ) + Nat.dist before after := by
      exact_mod_cast Nat.dist.triangle_inequality anchor before after
    have hbeforeQ : (Nat.dist anchor before : ℚ) ≤ 6 * b := by exact_mod_cast hbefore
    have hafter : (Nat.dist anchor after : ℚ) ≤ 10 * b := by
      linarith only [htriangle, hbeforeQ, herror, hbudget i]
    exact_mod_cast hafter
  constructor
  · apply wideActionList_complete
    · intro i
      have hgrid := bandRoundSpacing_wide_grid thetaExponent band initial i hM hPpos hbPower hPPower hscale
      exact ⟨hgrid.trans (dvd_mul_right _ _), hgrid.trans (dvd_mul_right _ _)⟩
    · intro i
      exact hanchor _ _ _ i (hpredicate.2.1 i).1 (herr i).1
    · intro i
      exact hanchor _ _ _ i (hpredicate.2.1 i).2 (herr i).2
  · intro i
    have hbefore := (hinitialGap i (action i)).trans
      ((bandChildEnvelope_lower b band initial i).2 action haction)
    have hspatial := stateLengthGap_spatial
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (rounded i) (action i)
    rw [← rationalStateGap_cast, ← rationalStateGap_cast] at hspatial
    have hspatialQ : |rationalStateGap
        (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (rounded i)| ≤
        |rationalStateGap (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (action i)| +
          (targetEndpointDistance (rounded i) (action i) : ℚ) := by exact_mod_cast hspatial
    have hdistance := roundedBandAction_distance thetaExponent b band initial action i
    have hsym : targetEndpointDistance (rounded i) (action i) = targetEndpointDistance (action i) (rounded i) := by
      unfold targetEndpointDistance
      rw [Nat.dist_comm (rounded i).lo, Nat.dist_comm (rounded i).hi]
    rw [hsym] at hspatialQ
    have hscaled := mul_le_mul_of_nonneg_right htheta (henv i)
    nlinarith only [hbefore, hspatialQ, hdistance, hscaled]

/-- Moving the two endpoints of each interval charges at most their total
movement, including the outside connections. -/
theorem connectionBudget_pair_perturbation {n : ℕ}
    (pairs : List (TargetInterval n × TargetInterval n)) (beforeStart afterStart finish : ℕ) :
    connectionBudget afterStart (pairs.map Prod.snd) finish ≤
      connectionBudget beforeStart (pairs.map Prod.fst) finish + Nat.dist afterStart beforeStart +
        (pairs.map fun pair => targetEndpointDistance pair.1 pair.2).sum := by
  induction pairs generalizing beforeStart afterStart with
  | nil =>
    simp only [List.map_nil, List.sum_nil, connectionBudget, Nat.add_zero]
    have h := Nat.dist.triangle_inequality afterStart beforeStart finish
    omega
  | cons pair rest ih =>
    rcases pair with ⟨before, after⟩
    have htail := ih before.hi after.hi
    have hfirst := Nat.dist.triangle_inequality afterStart beforeStart before.lo
    have hsecond := Nat.dist.triangle_inequality afterStart before.lo after.lo
    rw [Nat.dist_comm after.hi before.hi] at htail
    simp only [List.map_cons, List.sum_cons, connectionBudget, targetEndpointDistance] at htail ⊢
    omega

theorem endpointActionConnection_perturbation {n M : ℕ} (r : TargetInterval n)
    (before after : Fin M → TargetInterval n) :
    endpointActionConnection r after ≤ endpointActionConnection r before +
      ∑ i, targetEndpointDistance (before i) (after i) := by
  have h := connectionBudget_pair_perturbation
    (List.ofFn fun i : Fin M => (before i, after i)) r.lo r.lo r.hi
  simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_def, Nat.dist_self, Nat.add_zero,
    endpointActionConnection] using h

/-- The returned rounded action pays at most `2 θ ∑ hᵢ` in actual
connection cost when its unrounded band action has zero connection. -/
theorem roundedBandAction_connection {n M : ℕ} (r : TargetInterval n)
    (thetaExponent b : ℕ) (band : List (Fin M → TargetInterval n))
    (initial : Fin M → TargetInterval n → ℚ) (action : Fin M → TargetInterval n)
    (hzero : endpointActionConnection r action = 0) :
    (endpointActionConnection r (roundedBandAction thetaExponent b band initial action) : ℚ) ≤
      2 * (2 : ℚ) ^ (-(thetaExponent : ℤ)) * ∑ i, bandChildEnvelope b band initial i := by
  have hnatural := endpointActionConnection_perturbation r action
    (roundedBandAction thetaExponent b band initial action)
  rw [hzero, Nat.zero_add] at hnatural
  have hcast : (endpointActionConnection r
      (roundedBandAction thetaExponent b band initial action) : ℚ) ≤
        ∑ i, (targetEndpointDistance (action i)
          (roundedBandAction thetaExponent b band initial action i) : ℚ) := by
    exact_mod_cast hnatural
  calc
    _ ≤ ∑ i, (targetEndpointDistance (action i)
        (roundedBandAction thetaExponent b band initial action i) : ℚ) := hcast
    _ ≤ ∑ i, 2 * (2 : ℚ) ^ (-(thetaExponent : ℤ)) * bandChildEnvelope b band initial i :=
      sum_le_sum fun i _ => roundedBandAction_distance thetaExponent b band initial action i
    _ = _ := by rw [mul_sum]

theorem canonicalRoundedBandAction_connection {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (thetaExponent b P : ℕ) (tau velocity : ℚ)
    (child initial : Fin M → TargetInterval ny → ℚ)
    (hnonempty : computedBandActions parent r b P tau
      ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child ≠ []) :
    let band := computedBandActions parent r b P tau
      ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child
    (endpointActionConnection r
      (canonicalRoundedBandAction thetaExponent b band hnonempty initial) : ℚ) ≤
      2 * (2 : ℚ) ^ (-(thetaExponent : ℤ)) * ∑ i, bandChildEnvelope b band initial i := by
  have hmem := List.head_mem hnonempty
  obtain ⟨_, _, _, hpredicate⟩ := computedBandActions_mem parent r b P tau
    ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child _ hmem
  exact roundedBandAction_connection r thetaExponent b _ initial _ hpredicate.1

/-- The initial table's literal spatial bound controls the value of every
returned rounded state. -/
theorem roundedBandAction_initialValue {ny M : ℕ} (thetaExponent b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → ℚ) (action : Fin M → TargetInterval ny)
    (L0 : ℚ) (hL0 : 0 ≤ L0)
    (hspatial : ∀ i s t, initial i s ≤ initial i t + L0 * targetEndpointDistance s t)
    (i : Fin M) :
    initial i (roundedBandAction thetaExponent b band initial action i) ≤ initial i (action i) +
      2 * L0 * (2 : ℚ) ^ (-(thetaExponent : ℤ)) * bandChildEnvelope b band initial i := by
  have h := hspatial i (roundedBandAction thetaExponent b band initial action i) (action i)
  have hsym : targetEndpointDistance (roundedBandAction thetaExponent b band initial action i) (action i) =
      targetEndpointDistance (action i) (roundedBandAction thetaExponent b band initial action i) := by
    unfold targetEndpointDistance
    rw [Nat.dist_comm (roundedBandAction thetaExponent b band initial action i).lo,
      Nat.dist_comm (roundedBandAction thetaExponent b band initial action i).hi]
  rw [hsym] at h
  have hmove := mul_le_mul_of_nonneg_left
    (roundedBandAction_distance thetaExponent b band initial action i) hL0
  nlinarith only [h, hmove]

theorem roundedBandAction_initialValue_le_twice {ny M : ℕ} (thetaExponent b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → ℚ) (action : Fin M → TargetInterval ny)
    (haction : action ∈ band) (L0 : ℚ) (hL0 : 0 ≤ L0)
    (hsmall : 2 * L0 * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ 1)
    (hspatial : ∀ i s t, initial i s ≤ initial i t + L0 * targetEndpointDistance s t)
    (i : Fin M) :
    initial i (roundedBandAction thetaExponent b band initial action i) ≤
      2 * bandChildEnvelope b band initial i := by
  have hbefore := (bandChildEnvelope_lower b band initial i).2 action haction
  have hafter := roundedBandAction_initialValue thetaExponent b band initial action L0 hL0 hspatial i
  have hmove := mul_le_mul_of_nonneg_right hsmall (bandChildEnvelope_pos b band initial i).le
  nlinarith only [hbefore, hafter, hmove]

/-- The canonical rounded action is close to every member of its actual
computed band, with distance measured at both child endpoints. -/
theorem canonicalRoundedBandAction_distance {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (thetaExponent b P : ℕ) (tau velocity : ℚ) (htau : 0 < tau)
    (child initial : Fin M → TargetInterval ny → ℚ)
    (hnonempty : computedBandActions parent r b P tau
      ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child ≠ [])
    (action : Fin M → TargetInterval ny)
    (haction : action ∈ computedBandActions parent r b P tau
      ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child) (i : Fin M) :
    let band := computedBandActions parent r b P tau
      ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child
    (targetEndpointDistance (action i)
      (canonicalRoundedBandAction thetaExponent b band hnonempty initial i) : ℚ) ≤
        6 * (2 : ℚ) ^ (-(thetaExponent : ℤ)) * bandChildEnvelope b band initial i := by
  let theta : ℚ := (2 : ℚ) ^ (-(thetaExponent : ℤ))
  let band := computedBandActions parent r b P tau theta velocity child
  let canonical := band.head hnonempty
  let rounded := canonicalRoundedBandAction thetaExponent b band hnonempty initial
  have htheta : 0 ≤ theta := (zpow_pos (by norm_num : (0 : ℚ) < 2) _).le
  have hcanonical : canonical ∈ band := List.head_mem hnonempty
  have hdiameter := computedBand_child_endpoint_diameter parent r b P tau theta velocity
    htau htheta child action canonical haction hcanonical i
  have hdiameterQ : (targetEndpointDistance (action i) (canonical i) : ℚ) ≤ 4 * theta * b / M := by
    exact_mod_cast hdiameter
  have hfloor := (bandChildEnvelope_lower b band initial i).1
  have hscaled := mul_le_mul_of_nonneg_left hfloor (mul_nonneg (by norm_num : (0 : ℚ) ≤ 4) htheta)
  have hdiameterEnvelope : (targetEndpointDistance (action i) (canonical i) : ℚ) ≤
      4 * theta * bandChildEnvelope b band initial i := by
    calc
      _ ≤ 4 * theta * ((b : ℚ) / M) := by convert hdiameterQ using 1; ring
      _ ≤ _ := hscaled
  have hround := roundedBandAction_distance thetaExponent b band initial canonical i
  change (targetEndpointDistance (canonical i) (rounded i) : ℚ) ≤
    2 * theta * bandChildEnvelope b band initial i at hround
  have htriangle : (targetEndpointDistance (action i) (rounded i) : ℚ) ≤
      targetEndpointDistance (action i) (canonical i) + targetEndpointDistance (canonical i) (rounded i) := by
    have hnatural : targetEndpointDistance (action i) (rounded i) ≤
        targetEndpointDistance (action i) (canonical i) + targetEndpointDistance (canonical i) (rounded i) := by
      unfold targetEndpointDistance
      have hlo := Nat.dist.triangle_inequality (action i).lo (canonical i).lo (rounded i).lo
      have hhi := Nat.dist.triangle_inequality (action i).hi (canonical i).hi (rounded i).hi
      omega
    exact_mod_cast hnatural
  change (targetEndpointDistance (action i) (rounded i) : ℚ) ≤
    6 * theta * bandChildEnvelope b band initial i
  linarith only [htriangle, hdiameterEnvelope, hround]

/-- The actual canonical rounded action satisfies the rounded-action
cost inequality uniformly for every actual band member. -/
theorem canonicalRoundedBandAction_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (thetaExponent b P : ℕ) (tau velocity : ℚ) (htau : 0 < tau)
    (child initial value : Fin M → TargetInterval ny → ℚ)
    (hnonempty : computedBandActions parent r b P tau
      ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child ≠ [])
    (action : Fin M → TargetInterval ny)
    (haction : action ∈ computedBandActions parent r b P tau
      ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child)
    (delta L : ℚ) (hL : 0 ≤ L)
    (hspatial : ∀ i s t, value i s ≤ (1 + delta) * value i t + L * targetEndpointDistance s t) :
    let band := computedBandActions parent r b P tau
      ((2 : ℚ) ^ (-(thetaExponent : ℤ))) velocity child
    rationalEndpointActionValue r (canonicalRoundedBandAction thetaExponent b band hnonempty initial) value ≤
      (1 + delta) * (∑ i, value i (action i)) +
        (6 * L + 2) * (2 : ℚ) ^ (-(thetaExponent : ℤ)) * ∑ i, bandChildEnvelope b band initial i := by
  let theta : ℚ := (2 : ℚ) ^ (-(thetaExponent : ℤ))
  let band := computedBandActions parent r b P tau theta velocity child
  let rounded := canonicalRoundedBandAction thetaExponent b band hnonempty initial
  have hchild (i : Fin M) : value i (rounded i) ≤ (1 + delta) * value i (action i) +
      6 * L * theta * bandChildEnvelope b band initial i := by
    have h := hspatial i (rounded i) (action i)
    have hsym : targetEndpointDistance (rounded i) (action i) = targetEndpointDistance (action i) (rounded i) := by
      unfold targetEndpointDistance
      rw [Nat.dist_comm (rounded i).lo, Nat.dist_comm (rounded i).hi]
    rw [hsym] at h
    have hmove := mul_le_mul_of_nonneg_left
      (canonicalRoundedBandAction_distance parent r thetaExponent b P tau velocity htau child initial
        hnonempty action haction i) hL
    nlinarith only [h, hmove]
  have hsum := sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin M))) => hchild i
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hsum
  have hconnection := canonicalRoundedBandAction_connection parent r thetaExponent b P tau velocity child initial hnonempty
  change (endpointActionConnection r rounded : ℚ) + ∑ i, value i (rounded i) ≤ _
  nlinarith only [hsum, hconnection]

end EditApproximation

end OAI
