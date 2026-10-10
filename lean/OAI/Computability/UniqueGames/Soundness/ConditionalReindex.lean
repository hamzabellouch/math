import OAI.Computability.UniqueGames.Foundations.SamplingLemmas
import OAI.Computability.UniqueGames.Soundness.ZeroInformationLemmas

namespace OAI

section

/-! Explicit hidden-coordinate enumeration in the actual conditional law. -/

namespace UniqueGamesTheorem.Soundness.ConditionalIncidences
open scoped BigOperators

def coordinateReindex {A B X : Type} (e : B ≃ A) : (A → X) ≃ (B → X) where
  toFun f := fun b => f (e b)
  invFun g := fun a => g (e.symm a)
  left_inv f := by
    funext a
    exact congrArg f (e.apply_symm_apply a)
  right_inv g := by
    funext b
    exact congrArg g (e.symm_apply_apply b)

theorem raw_conditional_incidence_reindex
    {P D O N : Type} [Fintype P] [DecidableEq P]
    [Fintype D] [Zero D] [DecidableEq D]
    [Fintype O] [DecidableEq O] [DecidableEq N]
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (hpos : 0 < Fintype.card (RawObservationFibre J name gamma observed))
    (r : ℕ) (e : Fin r ≃ PositionInside (zeroSet J gamma))
    (f : (Fin r → O × N) → ℚ) :
    average (fun sample : RawObservationFibre J name gamma observed =>
      f (fun i => incidence name (sample.val.2 (e i).val))) =
    average (fun fresh : Fin r → O × Fin 3 => f (fun i => incidence name (fresh i))) := by
  calc
    _ = average (fun fresh : InsideDraw (zeroSet J gamma) O =>
        f (fun i => incidence name (fresh (e i)))) :=
      raw_conditional_inside_average J name gamma observed hpos
        (fun fresh => f (fun i => incidence name (fresh (e i))))
    _ = _ := average_equiv (coordinateReindex e)
      (fun fresh : Fin r → O × Fin 3 => f (fun i => incidence name (fresh i)))

theorem raw_conditional_event_reindex_real
    {P D O N : Type} [Fintype P] [DecidableEq P]
    [Fintype D] [Zero D] [DecidableEq D]
    [Fintype O] [DecidableEq O] [DecidableEq N]
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (hpos : 0 < Fintype.card (RawObservationFibre J name gamma observed))
    (r : ℕ) (e : Fin r ≃ PositionInside (zeroSet J gamma))
    (event : (Fin r → O × N) → Prop) [DecidablePred event] :
    ((∑ sample : RawObservationFibre J name gamma observed,
      if event (fun i => incidence name (sample.val.2 (e i).val)) then (1:ℝ) else 0) /
        Fintype.card (RawObservationFibre J name gamma observed)) =
    ((∑ fresh : Fin r → O × Fin 3,
      if event (fun i => incidence name (fresh i)) then (1:ℝ) else 0) /
        Fintype.card (Fin r → O × Fin 3)) := by
  have hQ := raw_conditional_incidence_reindex J name gamma observed hpos r e
    (fun q => if event q then (1:ℚ) else 0)
  have hR := congrArg (fun q : ℚ => (q : ℝ)) hQ
  simpa only [average, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast,
    apply_ite, Rat.cast_one, Rat.cast_zero] using hR

end UniqueGamesTheorem.Soundness.ConditionalIncidences

end

end OAI
