import OAI.Analysis.FiniteFactor.OrbitSampling.Cube
import OAI.Analysis.FiniteFactor.OrbitSampling.WeightedTail

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

def sourceSamplingOrdered : Set SourceSamplingPair := {p | ∀ i, p.1 i ≤ p.2 i}

theorem sourceSamplingOrdered_measurable : MeasurableSet sourceSamplingOrdered := by
  simp only [sourceSamplingOrdered,Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_le
    ((measurable_pi_apply i).comp measurable_fst) ((measurable_pi_apply i).comp measurable_snd))

/-- The actual ordered restriction of the already constructed average. -/
def sourceSamplingTrimmed (I : Finset SourceCoordinate) (s : ℕ) (θ : SourceCoordinate → ℝ) :
    Measure SourceSamplingPair := (sourceSamplingUntrimmed I s θ).restrict sourceSamplingOrdered

instance sourceSamplingTrimmed_finite (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) : IsFiniteMeasure (sourceSamplingTrimmed I s θ) := by
  unfold sourceSamplingTrimmed
  infer_instance

theorem sourceSamplingTrimmed_ordered (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) : ∀ᵐ p ∂sourceSamplingTrimmed I s θ, ∀ i, p.1 i ≤ p.2 i :=
  ae_restrict_mem sourceSamplingOrdered_measurable

theorem sourceSamplingTrimmed_le (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) : sourceSamplingTrimmed I s θ ≤ sourceSamplingUntrimmed I s θ :=
  Measure.restrict_le_self

theorem sourceSamplingPowers_positive (s : ℕ) (n : ℤ) (hn : n ∈ sourceSamplingPowers s) :
    0 < n ∧ (n : ℝ) ≤ samplingQ (sourceBlockSize s) := by
  by_cases hs : 200000 ≤ sourceBlockSize s
  · exact ⟨((sourceSamplingPowers_spec s hs).1 n hn).2.2,
      ((sourceSamplingPowers_spec s hs).1 n hn).2.1⟩
  · simp [sourceSamplingPowers,hs] at hn

/-- Outside the finite prefix, every failure of global order is an actual
member of the source's countable tail-failure event. -/
theorem sourceSampling_order_failure_tail (s n : ℕ) (θ x : SourceCoordinate → ℝ)
    (hprefix : ∀ i ∈ sourceSamplingPrefix s, x i < coordinateRotate θ (n : ℤ) x i)
    (hbad : (x,coordinateRotate θ (n : ℤ) x) ∉ sourceSamplingOrdered) :
    x ∈ sourceTailOrderFailure θ (s+1) n := by
  have hb : ∃ i, coordinateRotate θ (n : ℤ) x i < x i := by
    simpa only [sourceSamplingOrdered,Set.mem_ofPred_eq,not_forall,not_le] using hbad
  obtain ⟨i,hi⟩ := hb
  have hout : i ∉ sourceSamplingPrefix s := fun hh => (hprefix i hh).asymm hi
  have hk : s+1 ≤ i.1 := by
    have hh := (CouplingParameters.mem_blockPrefix sourceBlockSize (s+1) i)
    change i ∉ CouplingParameters.blockPrefix sourceBlockSize (s+1) at hout
    have hnot : ¬ i.1 < s+1 := fun hi => hout (hh.mpr hi)
    omega
  rcases i with ⟨k,j⟩
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hk
  apply Set.mem_iUnion.mpr ⟨r,?_⟩
  apply Set.mem_iUnion.mpr ⟨j,?_⟩
  simpa only [coordinateRotate,Int.cast_natCast,Set.mem_ofPred_eq] using hi

/-- Discarded mass of each real summand obeys the preserved relative
weighted-tail estimate. This includes summands of mass zero. -/
theorem sourceSamplingSummand_discarded_le (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (n : ℤ)
    (hn : n ∈ sourceSamplingPowers s) :
    sourceSamplingSummand I s θ n sourceSamplingOrderedᶜ ≤
      sourceSamplingSummand I s θ n Set.univ *
        ENNReal.ofReal (4*(sourceBlockSize s : ℝ)^(-(sourceBlockSize s : ℝ)/20)) := by
  have hp := sourceSamplingPowers_positive s n hn
  have he : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hp.1.le
  have hm : Measurable (fun x => (x,coordinateRotate θ n x)) :=
    measurable_id.prodMk (coordinateRotate_preserving θ n).measurable
  rw [sourceSamplingSummand,Measure.map_apply hm sourceSamplingOrdered_measurable.compl,
    Measure.map_apply hm MeasurableSet.univ,Set.preimage_univ]
  have hc : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast he
  have hb := sourceSampling_weighted_tail_small I s θ hθ n.toNat (by rw [hc]; exact hp.2)
  rw [he] at hb
  apply le_trans _ hb
  apply measure_mono_ae
  filter_upwards [sourceSamplingWeightedMeasure_orders I s θ n] with x hx
  intro hb
  change (x,coordinateRotate θ n x) ∉ sourceSamplingOrdered at hb
  exact sourceSampling_order_failure_tail s n.toNat θ x (by simpa [he] using hx) (by simpa [he] using hb)

/-- The average loses at most the same relative error as each summand. -/
theorem sourceSamplingUntrimmed_discarded_le (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    sourceSamplingUntrimmed I s θ sourceSamplingOrderedᶜ ≤
      sourceSamplingUntrimmed I s θ Set.univ *
        ENNReal.ofReal (4*(sourceBlockSize s : ℝ)^(-(sourceBlockSize s : ℝ)/20)) := by
  simp only [sourceSamplingUntrimmed,Measure.smul_apply,smul_eq_mul,Measure.finsetSum_apply]
  rw [mul_assoc,Finset.sum_mul]
  exact mul_le_mul' le_rfl (Finset.sum_le_sum (fun n hn => sourceSamplingSummand_discarded_le I s θ hθ n hn))

end
end FiniteFactor

end OAI
