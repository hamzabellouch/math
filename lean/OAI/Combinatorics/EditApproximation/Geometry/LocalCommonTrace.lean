import OAI.Combinatorics.EditApproximation.Geometry.LocalCommonSeed
import OAI.Combinatorics.EditApproximation.Geometry.LocalTraceProgram

namespace OAI

/-! A common keyed source gives a lazy functional view of the seed trace.
Only the actual incoming seed is selected during execution. -/

namespace EditApproximation

section Trace

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

noncomputable def localCommonToScheduled (hP : 0 < P) : (passes : ℕ) →
    LocalCommonTrace (M := M) (J := J) (R := R) target N P H passes →
      LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H passes
  | 0, trace => trace
  | passes + 1, trace =>
    (localCommonToScheduled hP passes trace.1,
      fun seed => localCommonSample source target N P T H hP passes seed trace.2)

omit [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem localCommonToScheduled_seed (hP : 0 < P) : ∀ (passes : ℕ)
    (trace : LocalCommonTrace (M := M) (J := J) (R := R) target N P H passes),
    localTraceSeed source target N P T S H passes
        (localCommonToScheduled source target N P T H hP passes trace) =
      localCommonSeed source target N P T S H hP passes trace := by
  intro passes
  induction passes with
  | zero => intro trace; rfl
  | succ passes ih =>
    intro trace
    change localScheduledSeedNext source target N P T S H passes
        (localTraceSeed source target N P T S H passes
          (localCommonToScheduled source target N P T H hP passes trace.1))
        (localCommonSample source target N P T H hP passes
          (localTraceSeed source target N P T S H passes
            (localCommonToScheduled source target N P T H hP passes trace.1)) trace.2) =
      localScheduledSeedNext source target N P T S H passes
        (localCommonSeed source target N P T S H hP passes trace.1)
        (localCommonSample source target N P T H hP passes
          (localCommonSeed source target N P T S H hP passes trace.1) trace.2)
    rw [ih]

end Trace

end EditApproximation

end OAI
