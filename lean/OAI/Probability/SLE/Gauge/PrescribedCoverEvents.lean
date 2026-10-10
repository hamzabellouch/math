import OAI.Probability.SLE.Gauge.PrescribedCandidateCover

namespace OAI

/-! The finite terminal candidate family has measurable missed-cell cost.
Only this cost envelope is integrated; the spatial selection itself need
not be chosen measurably. -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
local instance prescribedCoverPathMeasurable : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance prescribedCoverPathBorel : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩

private lemma trace_inter_nonempty (f : C(ℝ≥0,ℂ)) (K A : Set ℂ) :
    ((Set.range f ∩ K) ∩ A).Nonempty ↔ ∃ t, f t∈K∩A := by
  constructor
  · rintro ⟨z,⟨⟨t,rfl⟩,hzK⟩,hzA⟩
    exact ⟨t,hzK,hzA⟩
  · rintro ⟨t,htK,htA⟩
    exact ⟨f t,⟨⟨t,rfl⟩,htK⟩,htA⟩

theorem prescribedMissedIndices_measurable
    {Ω : Type*} [MeasurableSpace Ω] (f : Ω → C(ℝ≥0,ℂ)) (hf : Measurable f)
    (ν : Ω → Measure ℂ) (hν : Measurable ν)
    {J : ℕ} (κ : ℝ) (W : Target.WienerLaw) (n : ℕ) (e : Fin J → ℤ×ℕ)
    (C c R : ℝ) (K : Set ℂ) (hK : IsClosed K) (ij : ℤ×ℤ) :
    MeasurableSet {ω | ij∈prescribedMissedIndices κ W n e C c R K (range (f ω)∩K) (ν ω)} := by
  classical
  let r := Target.entryRadius κ W (n,none)
  have hv : MeasurableSet {ω | ((range (f ω)∩K)∩prescribedFineCell r ij).Nonempty} := by
    simp_rw [trace_inter_nonempty]
    exact measurableSet_trace_hits_closed f hf (hK.inter isClosed_closedBall)
  have hm (j : Fin J) : MeasurableSet {ω |
      ν ω (closedBall (prescribedGridCenter r ij) (C*Target.entryRadius κ W (n,some (e j)))) <
      ENNReal.ofReal (c*Target.entryValue (n,some (e j))*
        (Target.entryRadius κ W (n,some (e j)))^Target.d κ)} :=
    measurableSet_lt ((Measure.measurable_coe isClosed_closedBall.measurableSet).comp hν)
      measurable_const
  have hall := MeasurableSet.iInter hm
  have hpair := hv.inter hall
  by_cases hij : ij∈prescribedGridIndex R r K
  · convert hpair using 1
    ext ω
    simp only [prescribedMissedIndices,Finset.mem_filter,hij,true_and,mem_inter_iff,
      mem_iInter,mem_ofPred_eq,r]
  · have heq : {ω | ij∈prescribedMissedIndices κ W n e C c R K (range (f ω)∩K) (ν ω)}=∅ := by
      ext ω
      have hij' : ij∉prescribedGridIndex R (Target.entryRadius κ W (n,none)) K := hij
      simp only [prescribedMissedIndices,Finset.mem_filter,hij',false_and,mem_ofPred_eq,mem_empty_iff_false]
    rw [heq]
    exact MeasurableSet.empty

theorem prescribed_missed_cost_measurable
    {Ω : Type*} [MeasurableSpace Ω] (f : Ω → C(ℝ≥0,ℂ)) (hf : Measurable f)
    (ν : Ω → Measure ℂ) (hν : Measurable ν)
    {J : ℕ} (κ : ℝ) (W : Target.WienerLaw) (n : ℕ) (e : Fin J → ℤ×ℕ)
    (C c R : ℝ) (K : Set ℂ) (hK : IsClosed K) (a : ℝ≥0∞) :
    Measurable (fun ω =>
      (prescribedMissedIndices κ W n e C c R K (range (f ω)∩K) (ν ω)).card*a) := by
  classical
  let I := prescribedGridIndex R (Target.entryRadius κ W (n,none)) K
  let E (ij : ℤ×ℤ) := {ω | ij∈prescribedMissedIndices κ W n e C c R K (range (f ω)∩K) (ν ω)}
  have hE (ij) : MeasurableSet (E ij) := prescribedMissedIndices_measurable f hf ν hν κ W n e C c R K hK ij
  have heq (ω) :
      (prescribedMissedIndices κ W n e C c R K (range (f ω)∩K) (ν ω)).card*a =
      ∑ ij∈I, (E ij).indicator (fun _ => a) ω := by
    rw [← nsmul_eq_mul,← Finset.sum_const]
    rw [prescribedMissedIndices,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ij hij
    by_cases h : ω∈E ij
    · rw [indicator_of_mem h]
      rw [ite_eq_left]
      exact (Finset.mem_filter.mp h).2
    · rw [indicator_of_notMem h]
      rw [ite_eq_right]
      intro hp
      exact h (Finset.mem_filter.mpr ⟨hij,hp⟩)
  simp_rw [heq]
  exact Finset.measurable_sum I (fun ij _ => measurable_const.indicator (hE ij))

end SLEExactGauge

end

end OAI
