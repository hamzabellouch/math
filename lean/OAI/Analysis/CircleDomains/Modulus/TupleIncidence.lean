import OAI.Analysis.CircleDomains.Selection.TupleReference

namespace OAI

/-! Incidence of a tuple with a fixed dust point. A free point whose
individual level sections are null has a null incident-tuple set. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X]

def tupleIncident (H : ℕ → Set (UnitAddCircle × X)) (x : X) : Set LevelTuple :=
  {q | ∃ j : Fin (q.1 + 1), (q.2.2 j, x) ∈ H (q.2.1 j)}

theorem isClosed_tupleIncident {H : ℕ → Set (UnitAddCircle × X)}
    (hH : ∀ i, IsClosed (H i)) (x : X) : IsClosed (tupleIncident H x) := by
  change IsClosed {q : Σ n : ℕ, (Fin (n + 1) → ℕ) × (Fin (n + 1) → UnitAddCircle) |
    ∃ j : Fin (q.1 + 1), (q.2.2 j, x) ∈ H (q.2.1 j)}
  apply isClosed_sigma_iff.mpr
  intro n
  change IsClosed {q : (Fin (n + 1) → ℕ) × (Fin (n + 1) → UnitAddCircle) |
    ∃ j, (q.2 j, x) ∈ H (q.1 j)}
  simp only [ofPred_exists]
  apply isClosed_iUnion_of_finite
  intro j
  exact (isClosed_labeledLevelGraph hH).preimage
    (show Continuous (fun q : (Fin (n + 1) → ℕ) × (Fin (n + 1) → UnitAddCircle) =>
      (q.1 j, (q.2 j, x))) from
      ((continuous_apply j).comp continuous_fst).prodMk
        (((continuous_apply j).comp continuous_snd).prodMk continuous_const))

omit [TopologicalSpace X] in
theorem tupleIncident_fiber_null (H : ℕ → Set (UnitAddCircle × X)) (x : X)
    (hx : ∀ i, volume {t : UnitAddCircle | (t, x) ∈ H i} = 0) (i : TupleType) :
    volume (tupleFiber i ⁻¹' tupleIncident H x) = 0 := by
  have heq : tupleFiber i ⁻¹' tupleIncident H x =
      ⋃ j : Fin (i.1 + 1), {t : Fin (i.1 + 1) → UnitAddCircle | (t j, x) ∈ H (i.2 j)} := by
    ext t
    simp only [mem_iUnion]
    rfl
  rw [heq]
  apply measure_iUnion_null
  intro j
  exact Measure.pi_eval_preimage_null (fun _ : Fin (i.1 + 1) =>
    (volume : Measure UnitAddCircle)) (hx (i.2 j))

theorem tupleReference_incident_null {H : ℕ → Set (UnitAddCircle × X)}
    (hH : ∀ i, IsClosed (H i)) (ω : TupleType → ℝ≥0∞) (x : X)
    (hx : ∀ i, volume {t : UnitAddCircle | (t, x) ∈ H i} = 0) :
    tupleReference ω (tupleIncident H x) = 0 := by
  rw [tupleReference_apply ω (isClosed_tupleIncident hH x).measurableSet,
    ENNReal.tsum_eq_zero]
  intro i
  rw [tupleIncident_fiber_null H x hx i, mul_zero]

end CircleDomainRigidity

end

end OAI
