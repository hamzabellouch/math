import OAI.Combinatorics.EditApproximation.Numerics.RationalPrefix
import OAI.Combinatorics.EditApproximation.Geometry.Bands
import OAI.Combinatorics.EditApproximation.Geometry.WideActions
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# The literal finite predicted band

The band is a rationally decidable filter of the enumerated wide actions.
Its internal-cut diameter follows from the actual finite prefix predictor,
without assuming a predictor Lipschitz contract.
-/

namespace EditApproximation









theorem computedBandActions_mem {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (tau theta velocity : ℚ)
    (child : Fin M → TargetInterval ny → ℚ) (states : Fin M → TargetInterval ny)
    (hstates : states ∈ computedBandActions parent r b P tau theta velocity child) :
    ∃ hnonempty : wideActionList M parent r b P ≠ [],
      states ∈ wideActionList M parent r b P ∧ |velocity| ≤ 1 - tau ∧
        bandActionPredicate parent r b tau theta velocity (wideActionList M parent r b P) hnonempty child states := by
  by_cases hempty : wideActionList M parent r b P = []
  · simp only [computedBandActions, dite_eq_left hempty, List.not_mem_nil] at hstates
  · by_cases hvelocity : |velocity| ≤ 1 - tau
    · simp only [computedBandActions, dite_eq_right hempty, ite_eq_left hvelocity] at hstates
      obtain ⟨hmem, hpredicate⟩ := List.mem_filter.mp hstates
      exact ⟨hempty, hmem, hvelocity, of_decide_eq_true hpredicate⟩
    · simp only [computedBandActions, dite_eq_right hempty, ite_eq_right hvelocity,
        List.not_mem_nil] at hstates

theorem computedBandActions_complete {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (tau theta velocity : ℚ)
    (child : Fin M → TargetInterval ny → ℚ) (states : Fin M → TargetInterval ny)
    (hnonempty : wideActionList M parent r b P ≠ [])
    (hstates : states ∈ wideActionList M parent r b P) (hvelocity : |velocity| ≤ 1 - tau)
    (hpredicate : bandActionPredicate parent r b tau theta velocity
      (wideActionList M parent r b P) hnonempty child states) :
    states ∈ computedBandActions parent r b P tau theta velocity child := by
  simp only [computedBandActions, dite_eq_right hnonempty, ite_eq_left hvelocity]
  exact List.mem_filter.mpr ⟨hstates, decide_eq_true hpredicate⟩

theorem computedBand_cut_diameter {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (tau theta velocity : ℚ) (htau : 0 < tau)
    (child : Fin M → TargetInterval ny → ℚ) (states states' : Fin M → TargetInterval ny)
    (hstates : states ∈ computedBandActions parent r b P tau theta velocity child)
    (hstates' : states' ∈ computedBandActions parent r b P tau theta velocity child)
    (j : Fin M) (hj : 0 < j.val) :
    (Nat.dist (states j).lo (states' j).lo : ℝ) ≤ 2 * (theta : ℝ) * b / M := by
  obtain ⟨hnonempty, hmem, hvelocity, hpredicate⟩ :=
    computedBandActions_mem parent r b P tau theta velocity child states hstates
  obtain ⟨hnonempty', hmem', hvelocity', hpredicate'⟩ :=
    computedBandActions_mem parent r b P tau theta velocity child states' hstates'
  let predictor := fun p : ℝ => widePrefixMinimum parent r (wideActionList M parent r b P)
    hnonempty (fun i s => (child i s : ℝ)) j.val p
  have hvelocityR : |(velocity : ℝ)| ≤ 1 - (tau : ℝ) := by exact_mod_cast hvelocity
  have htauR : (0 : ℝ) < tau := by exact_mod_cast htau
  have hband (s : Fin M → TargetInterval ny)
      (hs : bandActionPredicate parent r b tau theta velocity (wideActionList M parent r b P) hnonempty child s) :
      inPredictedBand predictor ((r.lo : ℝ) - parent.lo) velocity tau
        ((theta : ℝ) * b / M) (bandCutShift parent s j) := by
    have h := hs.2.2 j hj
    have hR : ((|bandCutShift parent s j - ((r.lo : ℚ) - parent.lo) - velocity *
          rationalWidePrefixMinimum parent r (wideActionList M parent r b P) hnonempty child j.val
            (bandCutShift parent s j)| : ℚ) : ℝ) ≤ ((tau * theta * b / M : ℚ) : ℝ) :=
      Rat.cast_le.mpr h
    simp only [Rat.cast_abs, Rat.cast_sub, Rat.cast_natCast, Rat.cast_mul, Rat.cast_div,
      rationalWidePrefixMinimum_cast] at hR
    simpa only [inPredictedBand, predictor, mul_assoc, mul_div_assoc] using hR
  have hdiam := predicted_band_diameter htauR hvelocityR
    (widePrefixMinimum_lipschitz parent r (wideActionList M parent r b P) hnonempty
      (fun i s => (child i s : ℝ)) j.val _ _)
    (hband states hpredicate) (hband states' hpredicate')
  have hpoint : ((bandCutShift parent states j : ℚ) : ℝ) -
      ((bandCutShift parent states' j : ℚ) : ℝ) = (states j).lo - ((states' j).lo : ℝ) := by
    simp only [bandCutShift, Rat.cast_sub, Rat.cast_natCast]
    ring
  rw [hpoint, natural_distance_cast] at hdiam
  simpa only [mul_div_assoc, mul_assoc] using hdiam

end EditApproximation

end OAI
