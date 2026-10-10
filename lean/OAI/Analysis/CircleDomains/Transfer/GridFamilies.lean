import OAI.Analysis.CircleDomains.Transfer.GridCompatibility
import OAI.Analysis.CircleDomains.Transfer.ReciprocalGridSelection

namespace OAI

/-!
# Simultaneous compatibility of every lattice tuple

The finite-transfer construction needs one choice of shifts that avoids
every bad tuple formed from distinct labels and lattice levels. The
integer offsets constitute a countable family, so the individual
absolute-continuity conclusions hold simultaneously. In particular they
hold for the finite period-one grids at reciprocal-integer spacings.
-/

open Set MeasureTheory Function

namespace CircleDomainRigidity.FiniteTransfer

/-- All choices of lattice offsets and distinct labels simultaneously
avoid their prescribed completed-product null events. -/
theorem ae_all_grid_tuples_avoid_null_events {m : ℕ} {h : ℝ}
    (hh : 0 < h) (hsmall : h ≤ 1)
    (E : (d : ℕ) → (Fin (d + 1) → Fin m) →
      Set (UnitAddCircle × (Fin d → UnitAddCircle)))
    (hE : ∀ d labels, Injective labels →
      (volume.prod (Measure.pi (fun _ : Fin d => volume))) (E d labels) = 0) :
    ∀ᵐ θ ∂Measure.pi (fun _ : Fin m => shiftLaw h),
      ∀ (d : ℕ) (labels : Fin (d + 1) → Fin m), Injective labels →
      ∀ k : Fin (d + 1) → ℤ,
        (((θ (labels 0) + (k 0 : ℝ) * h : ℝ) : UnitAddCircle),
          fun i : Fin d =>
            ((θ (labels i.succ) + (k i.succ : ℝ) * h : ℝ) : UnitAddCircle)) ∉
          E d labels := by
  apply ae_all_iff.mpr
  intro d
  apply ae_all_iff.mpr
  intro labels
  by_cases hi : Injective labels
  · have hall := ae_all_iff.mpr (fun k : Fin (d + 1) → ℤ =>
      ae_grid_tuple_avoids_null_event hh hsmall labels hi
        (fun i => (k i : ℝ) * h) (E d labels) (hE d labels hi))
    exact hall.mono (fun _ hθ _ => hθ)
  · exact Filter.Eventually.of_forall (fun _ h => False.elim (hi h))

/-- Specialization to the actual product law of reciprocal-integer
grids. Compatibility is retained when the spacing is chosen later. -/
theorem ae_reciprocal_grid_tuples_avoid_null_events {m : ℕ} (N : ℕ)
    (E : (d : ℕ) → (Fin (d + 1) → Fin m) →
      Set (UnitAddCircle × (Fin d → UnitAddCircle)))
    (hE : ∀ d labels, Injective labels →
      (volume.prod (Measure.pi (fun _ : Fin d => volume))) (E d labels) = 0) :
    ∀ᵐ θ ∂reciprocalGridLaw m N,
      ∀ (d : ℕ) (labels : Fin (d + 1) → Fin m), Injective labels →
      ∀ k : Fin (d + 1) → ℤ,
        (((θ (labels 0) + (k 0 : ℝ) * reciprocalGridStep N : ℝ) : UnitAddCircle),
          fun i : Fin d => ((θ (labels i.succ) +
            (k i.succ : ℝ) * reciprocalGridStep N : ℝ) : UnitAddCircle)) ∉ E d labels :=
  ae_all_grid_tuples_avoid_null_events (reciprocalGridStep_pos N)
    (reciprocalGridStep_le_one N) E hE

end CircleDomainRigidity.FiniteTransfer

end OAI
