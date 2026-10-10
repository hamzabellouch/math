import OAI.Combinatorics.EditApproximation.Geometry.CommonArrayTrace

namespace OAI

/-! A final independent draw may be stored as the last array row. These
maps expose the literal product law used by the scheduled seed passes. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

variable {Seed Ω Δ : Type}

def commonArrayFinal (n : ℕ) (input : Seed × (Fin (n + 1) → Ω)) :
    CommonSeedTrace Seed (fun _ => Ω) n × Ω :=
  (commonArrayToTrace n (input.1, fun i => input.2 i.castSucc), input.2 (Fin.last n))

def commonFinalArray (n : ℕ) (input : CommonSeedTrace Seed (fun _ => Ω) n × Ω) :
    Seed × (Fin (n + 1) → Ω) :=
  let previous := commonTraceToArray n input.1
  (previous.1, Fin.snoc previous.2 input.2)

 theorem commonArrayFinal_inverse (n : ℕ) (input : Seed × (Fin (n + 1) → Ω)) :
    commonFinalArray n (commonArrayFinal n input) = input := by
  unfold commonFinalArray commonArrayFinal
  rw [commonTraceToArray_toTrace]
  apply Prod.ext
  · rfl
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

 theorem commonFinalArray_inverse (n : ℕ) (input : CommonSeedTrace Seed (fun _ => Ω) n × Ω) :
    commonArrayFinal n (commonFinalArray n input) = input := by
  rcases input with ⟨trace, last⟩
  unfold commonFinalArray commonArrayFinal
  simp only [Fin.snoc_last, Fin.snoc_castSucc]
  exact Prod.ext (commonArrayToTrace_toArray n trace) rfl

section Law

variable [Fintype Seed] [Fintype Ω] [DecidableEq Seed]
  [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (incoming : Measure Seed) [IsProbabilityMeasure incoming]
  (random : Measure Ω) [IsProbabilityMeasure random]

omit [DecidableEq Seed] [IsProbabilityMeasure incoming] in
theorem commonArrayFinal_law (n : ℕ) :
    (incoming.prod (Measure.pi fun _ : Fin (n + 1) => random)).map (commonArrayFinal (Ω := Ω) n) =
      (commonTraceLaw (fun _ => random) incoming n).prod random := by
  classical
  apply Measure.ext_of_singleton
  rintro ⟨trace, last⟩
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
  have hpre : commonArrayFinal (Ω := Ω) n ⁻¹' {(trace, last)} =
      {commonFinalArray n (trace, last)} := by
    ext input
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      rw [← h, commonArrayFinal_inverse]
    · rintro rfl
      exact commonFinalArray_inverse n (trace, last)
  rw [hpre]
  change (incoming.prod (Measure.pi fun _ : Fin (n + 1) => random))
    {((commonTraceToArray n trace).1, Fin.snoc (commonTraceToArray n trace).2 last)} = _
  rw [← Set.singleton_prod_singleton, Measure.prod_prod, Measure.pi_singleton,
    Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [← mul_assoc, ← commonArrayToTrace_atom incoming random n (commonTraceToArray n trace),
    commonArrayToTrace_toArray, ← Set.singleton_prod_singleton, Measure.prod_prod]

end Law

def mapCommonTrace (f : Ω → Δ) : (n : ℕ) →
    CommonSeedTrace Seed (fun _ => Ω) n → CommonSeedTrace Seed (fun _ => Δ) n
  | 0, seed => seed
  | n + 1, trace => (mapCommonTrace f n trace.1, f trace.2)

 theorem mapCommonTrace_array (f : Ω → Δ) (n : ℕ) (input : Seed × (Fin n → Ω)) :
    mapCommonTrace f n (commonArrayToTrace n input) =
      commonArrayToTrace n (input.1, fun i => f (input.2 i)) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext (ih _) rfl

section MapLaw

variable [Fintype Seed] [Fintype Ω] [Fintype Δ] [DecidableEq Seed]
  [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [MeasurableSpace Δ] [MeasurableSingletonClass Δ]
  (incoming : Measure Seed) [IsProbabilityMeasure incoming]
  (random : Measure Ω) [IsProbabilityMeasure random]

omit [Fintype Δ] [DecidableEq Seed] [MeasurableSingletonClass Δ]
  [IsProbabilityMeasure incoming] [IsProbabilityMeasure random] in
 theorem mapCommonTrace_law (f : Ω → Δ) (n : ℕ) :
    (commonTraceLaw (fun _ => random) incoming n).map (mapCommonTrace f n) =
      commonTraceLaw (fun _ => random.map f) incoming n := by
  induction n with
  | zero => exact Measure.map_id
  | succ n ih =>
    change ((commonTraceLaw (fun _ => random) incoming n).prod random).map
      (Prod.map (mapCommonTrace f n) f) = _
    rw [← Measure.map_prod_map _ _ (measurable_of_finite _) (measurable_of_finite _), ih]
    rfl

end MapLaw

end EditApproximation

end OAI
