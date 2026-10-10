import OAI.Combinatorics.EditApproximation.Geometry.CommonSeedTrace
import Mathlib.MeasureTheory.Constructions.Pi

namespace OAI

/-! A finite array of fresh pass draws is equivalent to the sequential
common-source trace. The conversion has exactly the nested product law. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

variable {Seed Ω : Type}

def commonArrayToTrace : (n : ℕ) → Seed × (Fin n → Ω) → CommonSeedTrace Seed (fun _ => Ω) n
  | 0, input => input.1
  | n + 1, input => (commonArrayToTrace n (input.1, fun i => input.2 i.castSucc), input.2 (Fin.last n))

def commonTraceToArray : (n : ℕ) → CommonSeedTrace Seed (fun _ => Ω) n → Seed × (Fin n → Ω)
  | 0, seed => (seed, Fin.elim0)
  | n + 1, trace =>
    let previous := commonTraceToArray n trace.1
    (previous.1, Fin.snoc previous.2 trace.2)

 theorem commonTraceToArray_toTrace (n : ℕ) (input : Seed × (Fin n → Ω)) :
    commonTraceToArray n (commonArrayToTrace n input) = input := by
  induction n with
  | zero =>
    apply Prod.ext
    · rfl
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    simp only [commonArrayToTrace, commonTraceToArray, ih]
    apply Prod.ext
    · rfl
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp

 theorem commonArrayToTrace_toArray (n : ℕ) (trace : CommonSeedTrace Seed (fun _ => Ω) n) :
    commonArrayToTrace n (commonTraceToArray n trace) = trace := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases trace with ⟨trace, last⟩
    simp only [commonArrayToTrace, commonTraceToArray, Fin.snoc_last, Fin.snoc_castSucc]
    exact Prod.ext (ih trace) rfl

section Law

variable [Fintype Seed] [Fintype Ω] [DecidableEq Seed]
  [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (incoming : Measure Seed) [IsProbabilityMeasure incoming]
  (random : Measure Ω) [IsProbabilityMeasure random]

omit [Fintype Seed] [DecidableEq Seed] [MeasurableSingletonClass Seed]
  [MeasurableSingletonClass Ω] [IsProbabilityMeasure incoming] [IsProbabilityMeasure random] in
theorem commonArrayToTrace_atom (n : ℕ) (input : Seed × (Fin n → Ω)) :
    (commonTraceLaw (fun _ => random) incoming n) {commonArrayToTrace n input} =
      incoming {input.1} * ∏ i, random {input.2 i} := by
  induction n with
  | zero =>
    simp only [commonArrayToTrace, commonTraceLaw, Fin.prod_univ_zero, mul_one]
    rfl
  | succ n ih =>
    change ((commonTraceLaw (fun _ => random) incoming n).prod random)
      {(commonArrayToTrace n (input.1, fun i => input.2 i.castSucc), input.2 (Fin.last n))} = _
    rw [← Set.singleton_prod_singleton, Measure.prod_prod, ih, Fin.prod_univ_castSucc]
    exact mul_assoc _ _ _

omit [DecidableEq Seed] [IsProbabilityMeasure incoming] in
theorem commonArrayToTrace_law (n : ℕ) :
    (incoming.prod (Measure.pi fun _ : Fin n => random)).map (commonArrayToTrace (Ω := Ω) n) =
      commonTraceLaw (fun _ => random) incoming n := by
  classical
  apply Measure.ext_of_singleton
  intro trace
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
  have hpre : commonArrayToTrace (Ω := Ω) n ⁻¹' {trace} = {commonTraceToArray n trace} := by
    ext input
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      rw [← h, commonTraceToArray_toTrace]
    · rintro rfl
      exact commonArrayToTrace_toArray n trace
  rw [hpre]
  change (incoming.prod (Measure.pi fun _ : Fin n => random))
    {((commonTraceToArray n trace).1, (commonTraceToArray n trace).2)} = _
  rw [← Set.singleton_prod_singleton, Measure.prod_prod, Measure.pi_singleton]
  have h := commonArrayToTrace_atom incoming random n (commonTraceToArray n trace)
  rw [commonArrayToTrace_toArray] at h
  exact h.symm

end Law

end EditApproximation

end OAI
