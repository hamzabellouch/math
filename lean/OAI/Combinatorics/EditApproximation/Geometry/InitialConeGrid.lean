import OAI.Combinatorics.EditApproximation.Geometry.InitialCones
import OAI.Combinatorics.EditApproximation.Geometry.Grid
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# A rounded eligible center for each positive-cost query

This uses the actual natural division grid and the dyadic scale selected
from the integer edit cost. It supplies a finite-family witness for the
initial cone minimum.
-/

namespace EditApproximation





theorem cost_dyadicScale (c N : ℕ) (hc : 0 < c) (hcN : c ≤ N) :
    let b := 2 ^ Nat.log 2 c
    b ∈ dyadicScales N ∧ b ≤ c ∧ c < 2 * b := by
  dsimp only
  refine ⟨?_, Nat.pow_log_le_self 2 hc.ne', ?_⟩
  · apply List.mem_map.mpr
    refine ⟨Nat.log 2 c, List.mem_range.mpr ?_, rfl⟩
    exact Nat.lt_succ_of_le (Nat.log_mono_right hcN)
  · have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) c
    simpa only [pow_succ, mul_comm] using h

theorem rounded_seedGrid_error {n : ℕ} (b P : ℕ) (hP : 0 < P)
    (q : TargetInterval n) :
    (targetEndpointDistance q (roundInterval (seedGridSpacing b P) q) : ℚ) * P ≤ 2 * b := by
  by_cases hg : b / P ≤ 1
  · have he : targetEndpointDistance q (roundInterval (seedGridSpacing b P) q) = 0 := by
      simp [targetEndpointDistance, roundInterval, seedGridSpacing, max_eq_left hg]
    rw [he]
    simp only [Nat.cast_zero, zero_mul]
    positivity
  · have hquot : 1 ≤ b / P := by omega
    have he := roundInterval_error (b / P) (by omega) q
    have hdiv := Nat.div_mul_le_self b P
    have hprod : targetEndpointDistance q (roundInterval (seedGridSpacing b P) q) * P ≤ 2 * b := by
      unfold seedGridSpacing
      rw [max_eq_right hquot]
      change (Nat.dist q.lo (roundInterval (b / P) q).lo +
        Nat.dist q.hi (roundInterval (b / P) q).hi) * P ≤ 2 * b
      nlinarith
    exact_mod_cast hprod

theorem roundInterval_on_grid {n : ℕ} (g : ℕ) (q : TargetInterval n) :
    g ∣ (roundInterval g q).lo ∧ g ∣ (roundInterval g q).hi := by
  exact ⟨dvd_mul_right _ _, dvd_mul_right _ _⟩

theorem rounded_initial_center_numeric {c cr Ur b P A F e : ℚ}
    (hb : 0 < b) (hbc : b ≤ c) (hcb : c < 2 * b)
    (hP : 66 ≤ P) (hA : 1 ≤ A) (hF : 0 ≤ F) (he : 0 ≤ e)
    (hgrid : e * P ≤ 2 * b) (hcost : |c - cr| ≤ e)
    (hseed : cr ≤ Ur ∧ Ur ≤ A * cr) :
    b / 2 ≤ Ur ∧ Ur ≤ 4 * A * b ∧ F * cr + 32 * F * e ≤ 2 * F * c := by
  have hcosts := abs_le.mp hcost
  have hsmall : 33 * e ≤ b := by nlinarith
  have hcrlo : b / 2 ≤ cr := by linarith
  have hcrhi : cr ≤ 4 * b := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hcrhi (by linarith : 0 ≤ A)
  have hcone := mul_le_mul_of_nonneg_left (show cr + 32 * e ≤ 2 * c by linarith) hF
  exact ⟨hcrlo.trans hseed.1, hseed.2.trans (by nlinarith), by nlinarith⟩

theorem stateEditCost_distance_abs {α : Type*} (source target : List α)
    (q r : TargetInterval target.length) :
    |(stateEditCost source target q : ℚ) - stateEditCost source target r| ≤
      targetEndpointDistance q r := by
  have hqr : (stateEditCost source target q : ℚ) ≤
      stateEditCost source target r + targetEndpointDistance q r := by
    exact_mod_cast stateEditCost_spatial source target q r
  have hrq : (stateEditCost source target r : ℚ) ≤
      stateEditCost source target q + targetEndpointDistance q r := by
    have h := stateEditCost_spatial source target r q
    simpa only [targetEndpointDistance, Nat.dist_comm] using (show
      (stateEditCost source target r : ℚ) ≤ stateEditCost source target q +
        targetEndpointDistance r q by exact_mod_cast h)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem rounded_initial_cone_witness {α : Type*} (source target : List α)
    (U : TargetInterval target.length → ℕ) (N P F : ℕ) (A a : ℚ)
    (q : TargetInterval target.length) (hcost : 0 < stateEditCost source target q)
    (hN : stateEditCost source target q ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F)
    (hA : 1 ≤ A) (ha : 1 ≤ a)
    (hseed : ∀ r, stateEditCost source target r ≤ U r ∧
      (U r : ℚ) ≤ A * stateEditCost source target r)
    (hfactor : A ≤ a * F) :
    ∃ b ∈ dyadicScales N, ∃ r : TargetInterval target.length,
      seedGridSpacing b P ∣ r.lo ∧ seedGridSpacing b P ∣ r.hi ∧
      (b : ℚ) / 2 ≤ U r ∧ (U r : ℚ) ≤ 4 * A * b ∧
      initialConeValue source target U a (32 * F) q r ≤
        2 * F * stateEditCost source target q := by
  let c := stateEditCost source target q
  let b := 2 ^ Nat.log 2 c
  let r := roundInterval (seedGridSpacing b P) q
  have hscale := cost_dyadicScale c N hcost hN
  have he := rounded_seedGrid_error b P (by omega) q
  have hnumeric := rounded_initial_center_numeric
    (c := (c : ℚ)) (cr := stateEditCost source target r) (Ur := U r)
    (b := (b : ℚ)) (P := (P : ℚ)) (A := A) (F := (F : ℚ))
    (e := targetEndpointDistance q r)
    (by dsimp only [b]; positivity) (by exact_mod_cast hscale.2.1)
    (by exact_mod_cast hscale.2.2) (by exact_mod_cast hP) hA (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) he (stateEditCost_distance_abs source target q r)
    ⟨by exact_mod_cast (hseed r).1, (hseed r).2⟩
  have hgap : |rationalStateGap source target r| ≤ (stateEditCost source target r : ℚ) := by
    have h := stateEditCost_length_lower source target r
    rw [← rationalStateGap_cast] at h
    exact_mod_cast h
  have hupper : (U r : ℚ) ≤ a * F * stateEditCost source target r :=
    (hseed r).2.trans (mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg _))
  have hscaled := (scaledSeedValue_bounds (U r) (stateEditCost source target r)
    F a _ ha hF (hseed r).1 hupper hgap).2
  refine ⟨b, hscale.1, r, (roundInterval_on_grid _ q).1,
    (roundInterval_on_grid _ q).2, hnumeric.1, hnumeric.2.1, ?_⟩
  unfold initialConeValue
  linarith [hnumeric.2.2]

end EditApproximation

end OAI
