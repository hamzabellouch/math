import OAI.Analysis.CircleDomains.Selection.TaggedPointContacts

namespace OAI

/-! Null sets of scalar levels induce null sets of finite tagged tuples.
This also supplies a Borel description when the null sets are envelopes. -/

open Set Function MeasureTheory Filter
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem measurableEmbedding_tupleFiber (i : TupleType) : MeasurableEmbedding (tupleFiber i) := by
  apply (measurable_tupleFiber i).measurableEmbedding
  intro x y h
  have hp : (i.2, x) = (i.2, y) :=
    sigma_mk_injective (β := fun n : ℕ =>
      (Fin (n + 1) → ℕ) × (Fin (n + 1) → UnitAddCircle)) h
  exact congrArg Prod.snd hp

theorem levelTuple_eq_iUnion_fibers (A : Set LevelTuple) :
    A = ⋃ i : TupleType, tupleFiber i '' (tupleFiber i ⁻¹' A) := by
  ext q
  constructor
  · intro hq
    rcases q with ⟨n, l, t⟩
    exact mem_iUnion.mpr ⟨⟨n, l⟩, t, hq, rfl⟩
  · intro h
    obtain ⟨i, t, ht, rfl⟩ := mem_iUnion.mp h
    exact ht

theorem measurableSet_levelTuple_of_fibers (A : Set LevelTuple)
    (hA : ∀ i : TupleType, MeasurableSet (tupleFiber i ⁻¹' A)) : MeasurableSet A := by
  rw [levelTuple_eq_iUnion_fibers A]
  exact MeasurableSet.iUnion fun i => (measurableEmbedding_tupleFiber i).measurableSet_image.mpr (hA i)

def tuplesWithBadLevel (N : ℕ → Set UnitAddCircle) : Set LevelTuple :=
  {q | ∃ j : Fin (q.1 + 1), q.2.2 j ∈ N (q.2.1 j)}

theorem measurableSet_tuplesWithBadLevel (N : ℕ → Set UnitAddCircle)
    (hN : ∀ i, MeasurableSet (N i)) : MeasurableSet (tuplesWithBadLevel N) := by
  apply measurableSet_levelTuple_of_fibers
  intro i
  change MeasurableSet {t : Fin (i.1 + 1) → UnitAddCircle | ∃ j, t j ∈ N (i.2 j)}
  simp only [ofPred_exists]
  exact MeasurableSet.iUnion fun j => (hN (i.2 j)).preimage (measurable_pi_apply j)

theorem tupleReference_badLevel_null (ω : TupleType → ℝ≥0∞)
    (N : ℕ → Set UnitAddCircle) (hN : ∀ i, MeasurableSet (N i))
    (hzero : ∀ i, volume (N i) = 0) : tupleReference ω (tuplesWithBadLevel N) = 0 := by
  rw [tupleReference_apply ω (measurableSet_tuplesWithBadLevel N hN), ENNReal.tsum_eq_zero]
  intro i
  have he : tupleFiber i ⁻¹' tuplesWithBadLevel N =
      ⋃ j : Fin (i.1 + 1), {t : Fin (i.1 + 1) → UnitAddCircle | t j ∈ N (i.2 j)} := by
    ext t
    simp only [mem_iUnion]
    rfl
  rw [he]
  have hz : volume (⋃ j : Fin (i.1 + 1),
      {t : Fin (i.1 + 1) → UnitAddCircle | t j ∈ N (i.2 j)}) = 0 := by
    apply measure_iUnion_null
    intro j
    exact Measure.pi_eval_preimage_null
      (fun _ : Fin (i.1 + 1) => (volume : Measure UnitAddCircle)) (hzero (i.2 j))
  rw [hz, mul_zero]

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem ae_slots_zero_on_null_tuples (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (τ : Measure LevelTuple)
    (hτ : meanCodeTuple d P ≪ τ) (A : Set LevelTuple) (hA : MeasurableSet A)
    (hz : τ A = 0) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ k, slotTupleMeasure (Γ.val.2 k) A = 0 := by
  apply ae_all_iff.mpr
  intro k
  have h := slotLaw_absolutelyContinuous d P τ hτ k hz
  rw [slotLaw_apply d P k hA] at h
  exact (lintegral_eq_zero_iff ((Measure.measurable_coe hA).comp
    (measurable_baseCodeSlot d k))).mp h

theorem no_tag_level_in_null_set (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (ω : TupleType → ℝ≥0∞)
    (hτ : meanCodeTuple d P ≪ tupleReference ω)
    (N : ℕ → Set UnitAddCircle) (hN : ∀ i, MeasurableSet (N i))
    (hzero : ∀ i, volume (N i) = 0) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
      ∀ k q, Γ.val.2 k = Sum.inr q → ∀ j, q.2.2.1 j ∉ N (q.2.1 j) := by
  filter_upwards [ae_slots_zero_on_null_tuples d P (tupleReference ω) hτ
    (tuplesWithBadLevel N) (measurableSet_tuplesWithBadLevel N hN)
    (tupleReference_badLevel_null ω N hN hzero)] with Γ hΓ
  intro k q hq j hj
  have hmem : tagDataTuple q ∈ tuplesWithBadLevel N := ⟨j, hj⟩
  have h := hΓ k
  rw [hq, slotTupleMeasure, Sum.elim_inr,
    Measure.dirac_apply' _ (measurableSet_tuplesWithBadLevel N hN),
    indicator_of_mem hmem, Pi.one_apply] at h
  exact one_ne_zero h

end CircleDomainRigidity

end

end OAI
