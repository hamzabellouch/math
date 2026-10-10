import OAI.Analysis.CircleDomains.Selection.TupleExclusions

namespace OAI

/-! The tuple reference measure is a positive weighted sum of Lebesgue
measures on the finite tuple tori, indexed by label type rather than slot. -/

open Set MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

abbrev TupleType := Σ n : ℕ, Fin (n + 1) → ℕ

def tupleFiber (i : TupleType) (t : Fin (i.1 + 1) → UnitAddCircle) : LevelTuple :=
  ⟨i.1, i.2, t⟩

theorem continuous_tupleFiber (i : TupleType) : Continuous (tupleFiber i) :=
  continuous_sigmaMk.comp (continuous_const.prodMk continuous_id)

theorem measurable_tupleFiber (i : TupleType) : Measurable (tupleFiber i) :=
  Continuous.measurable (α := Fin (i.1 + 1) → UnitAddCircle) (γ := LevelTuple)
    (continuous_tupleFiber i)

def tupleReference (ω : TupleType → ℝ≥0∞) : Measure LevelTuple :=
  Measure.sum (fun i => ω i • (volume.map (tupleFiber i)))

theorem tupleReference_apply (ω : TupleType → ℝ≥0∞)
    {A : Set LevelTuple} (hA : MeasurableSet A) :
    tupleReference ω A = ∑' i, ω i * volume (tupleFiber i ⁻¹' A) := by
  simp only [tupleReference, Measure.sum_apply _ hA, Measure.smul_apply,
    smul_eq_mul, Measure.map_apply (measurable_tupleFiber _) hA]

theorem tupleReference_univ (ω : TupleType → ℝ≥0∞) :
    tupleReference ω univ = ∑' i, ω i := by
  rw [tupleReference_apply ω MeasurableSet.univ]
  apply tsum_congr
  intro i
  have hv : (volume : Measure (Fin (i.1 + 1) → UnitAddCircle)) univ = 1 := by
    change (Measure.pi (fun _ : Fin (i.1 + 1) => (volume : Measure UnitAddCircle))) univ = 1
    rw [Measure.pi_univ]
    simp [AddCircle.measure_univ]
  simp only [preimage_univ, hv, mul_one]

theorem finite_tupleReference {ω : TupleType → ℝ≥0∞} (hω : (∑' i, ω i) < ∞) :
    IsFiniteMeasure (tupleReference ω) := ⟨by rwa [tupleReference_univ]⟩

theorem lintegral_tupleReference (ω : TupleType → ℝ≥0∞)
    (f : LevelTuple → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ t, f t ∂tupleReference ω =
      ∑' i, ω i * ∫⁻ t, f (tupleFiber i t) := by
  rw [tupleReference, lintegral_sum_measure]
  simp only [lintegral_smul_measure, smul_eq_mul,
    lintegral_map hf (measurable_tupleFiber _)]

theorem tupleReference_fiber_null {ω : TupleType → ℝ≥0∞}
    (hω : ∀ i, ω i ≠ 0) {A : Set LevelTuple} (hA : MeasurableSet A)
    (hnull : tupleReference ω A = 0) (i : TupleType) :
    volume (tupleFiber i ⁻¹' A) = 0 := by
  rw [tupleReference_apply ω hA, ENNReal.tsum_eq_zero] at hnull
  exact (mul_eq_zero.mp (hnull i)).resolve_left (hω i)

theorem null_tupleInfiniteExclusions {ω : TupleType → ℝ≥0∞}
    (hω : ∀ i, ω i ≠ 0) {f : LevelTuple → ℝ≥0∞} (hf : Measurable f)
    (hint : (∫⁻ t, f t ^ 2 ∂tupleReference ω) < ∞) (n : ℕ) (l : Fin (n + 1) → ℕ) :
    volume (tupleInfiniteExclusions f n l) = 0 := by
  have hae : ∀ᵐ t ∂tupleReference ω, f t < ∞ := by
    filter_upwards [ae_lt_top (hf.pow_const 2) hint.ne] with t ht
    by_contra hn
    have he : f t = ∞ := top_unique (not_lt.mp hn)
    simp [he] at ht
  have hnull : tupleReference ω {t | f t = ∞} = 0 := by
    simpa only [ae_iff, not_lt, top_le_iff] using hae
  exact tupleReference_fiber_null hω (hf (measurableSet_singleton ∞)) hnull ⟨n, l⟩

end CircleDomainRigidity

end

end OAI
