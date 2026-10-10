import OAI.NumberTheory.PrimePackets.ConditionalOrbitEntropy

namespace OAI

/-! # Conditional entropy increments of stationary finite observations -/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace PrimeDegreePackets

variable {Y α : Type*} [MeasurableSpace Y] [Fintype α]

def futureName (T : Y → Y) (P : Y → α) (N : ℕ) (y : Y) : Fin N → α :=
  orbitName T P N (T y)

omit [Fintype α] in
lemma futureName_measurable_fiber {T : Y → Y} (hT : Measurable T) {P : Y → α}
    (hP : ∀ a, MeasurableSet {y | P y = a}) (N : ℕ) (a : Fin N → α) :
    MeasurableSet {y | futureName T P N y = a} :=
  (orbitName_measurable_fiber hT hP N a).preimage hT

lemma orbitEntropy_succ_head (μ : Measure Y) (T : Y → Y) (P : Y → α) (N : ℕ) :
    observationEntropy μ (orbitName T P (N+1)) =
      observationEntropy μ (fun y => (P y,futureName T P N y)) := by
  rw [Nat.add_comm N 1, orbitName_add T P 1 N, observationEntropy_equiv, orbitName_one]
  have hi : Function.Injective
      (fun z : α × (Fin N → α) => ((fun _ : Fin 1 => z.1),z.2)) := by
    intro x y h
    have hfst : (fun _ : Fin 1 => x.1) = (fun _ : Fin 1 => y.1) :=
      congrArg (fun z : (Fin 1 → α) × (Fin N → α) => z.1) h
    have hsnd : x.2 = y.2 := congrArg (fun z : (Fin 1 → α) × (Fin N → α) => z.2) h
    exact Prod.ext (congrFun hfst 0) hsnd
  exact observationEntropy_injective μ (fun y => (P y,futureName T P N y)) _ hi

lemma futureConditionalEntropy_eq_sub
    (μ : Measure Y) {T : Y → Y} (hT : MeasurePreserving T μ μ) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) (N : ℕ) :
    conditionalObservationEntropy μ P (futureName T P N) =
      observationEntropy μ (orbitName T P (N+1)) -
      observationEntropy μ (orbitName T P N) := by
  unfold conditionalObservationEntropy
  rw [observationEntropy_swap μ (futureName T P N) P, ← orbitEntropy_succ_head]
  rw [show futureName T P N = fun y => orbitName T P N (T y) from rfl,
    observationEntropy_comp_preserving μ (orbitName T P N)
      (orbitName_measurable_fiber hT.measurable hP N) hT]

lemma futureConditionalEntropy_antitone
    (μ : Measure Y) [IsFiniteMeasure μ] {T : Y → Y} (hT : Measurable T) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) :
    Antitone (fun N => conditionalObservationEntropy μ P (futureName T P N)) := by
  apply antitone_nat_of_succ_le
  intro N
  exact conditionalObservationEntropy_coarsening_le μ P (futureName T P (N+1))
    (fun v (i : Fin N) => v i.castSucc) hP (futureName_measurable_fiber hT hP (N+1))

lemma sum_futureConditionalEntropy
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) (N : ℕ) :
    (∑ n ∈ Finset.range N, conditionalObservationEntropy μ P (futureName T P n)) =
      observationEntropy μ (orbitName T P N) := by
  induction N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, observationEntropy_unique]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, futureConditionalEntropy_eq_sub μ hT P hP]
      ring

theorem futureConditionalEntropy_tendsto_rate
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) :
    Tendsto (fun N => conditionalObservationEntropy μ P (futureName T P N)) atTop
      (𝓝 (observationEntropyRate μ T P)) := by
  let a := fun N => conditionalObservationEntropy μ P (futureName T P N)
  have hanti : Antitone a := futureConditionalEntropy_antitone μ hT.measurable P hP
  have hbdd : BddBelow (Set.range a) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨N,rfl⟩
    exact conditionalObservationEntropy_nonneg μ P _ hP
      (futureName_measurable_fiber hT.measurable hP N)
  have hlim := tendsto_atTop_ciInf hanti hbdd
  have hc := hlim.cesaro
  have hc' : Tendsto (fun N => observationEntropy μ (orbitName T P N) / (N : ℝ))
      atTop (𝓝 (⨅ n, a n)) := by
    simpa only [a, sum_futureConditionalEntropy μ hT P hP, div_eq_inv_mul] using hc
  have heq := tendsto_nhds_unique hc' (tendsto_observationEntropyRate μ hT P hP)
  rwa [heq] at hlim

end PrimeDegreePackets

end

end OAI
