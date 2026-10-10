import OAI.MeasureTheory.DyadicAvoidance.ExceptionalExpectation

namespace OAI

universe u_A u_K

noncomputable section

open MeasureTheory

namespace Problem310.RandomSetDensity

/-- A selector outcome chooses the terminal address read at each point. -/
def selectedSet {A : Type u_A} {K : Type u_K} (addr : A → ℝ → K) (z : A × (K → Bool)) : Set ℝ :=
  {x | z.2 (addr z.1 x) = true}

/-- Finite terminal tables preserve spatial measurability of the address map. -/
theorem measurableSet_selectedSet
    {A : Type u_A} {K : Type u_K} [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
    (addr : A → ℝ → K) (haddr : ∀ a, Measurable (addr a))
    (z : A × (K → Bool)) : MeasurableSet (selectedSet addr z) := by
  exact ((measurable_of_countable z.2).comp (haddr z.1)) (measurableSet_singleton true)

/-- Periodicity of terminal addresses gives periodicity of every realization. -/
theorem periodic_selectedSet
    {A : Type u_A} {K : Type u_K} (addr : A → ℝ → K)
    (haddr : ∀ a x, addr a (x + 1) = addr a x) (z : A × (K → Bool)) :
    ∀ x : ℝ, x + 1 ∈ selectedSet addr z ↔ x ∈ selectedSet addr z := by
  intro x
  simp only [selectedSet, Set.mem_ofPred_eq, haddr]

/-- Independence of terminal labels from selectors gives the same membership
probability at every spatial point, even with adaptively selected addresses. -/
theorem pointwise_probability_selectedSet
    {A : Type u_A} {K : Type u_K} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype K] (P : Measure A) [IsProbabilityMeasure P]
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (addr : A → ℝ → K) (x : ℝ) :
    (P.prod (Measure.pi (fun _ : K => ν))) {z | x ∈ selectedSet addr z} =
      ν {true} := by
  classical
  have hmeas : MeasurableSet {z : A × (K → Bool) | x ∈ selectedSet addr z} :=
    (Set.toFinite _).measurableSet
  rw [Measure.prod_apply hmeas]
  have hsection (a : A) :
      (Measure.pi (fun _ : K => ν)) {ω : K → Bool | ω (addr a x) = true} = ν {true} := by
    exact (measurePreserving_eval (fun _ : K => ν) (addr a x)).measure_preimage
      (measurableSet_singleton true).nullMeasurableSet
  change (∫⁻ a, (Measure.pi (fun _ : K => ν))
    {ω : K → Bool | ω (addr a x) = true} ∂P) = ν {true}
  simp only [hsection]
  simp

/-- Exact first-moment density identity for the random routed set. -/
theorem expected_density_selectedSet
    {A : Type u_A} {K : Type u_K} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
    (P : Measure A) [IsProbabilityMeasure P]
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (addr : A → ℝ → K) (haddr : ∀ a, Measurable (addr a)) :
    (∫⁻ z, volume (selectedSet addr z ∩ Set.Icc (0 : ℝ) 1)
      ∂(P.prod (Measure.pi (fun _ : K => ν)))) = ν {true} := by
  classical
  rw [Problem310.Auxiliary.expected_density_eq_pointwise_probability
    (P.prod (Measure.pi (fun _ : K => ν))) (selectedSet addr)
    (measurableSet_selectedSet addr haddr)]
  simp only [pointwise_probability_selectedSet P ν addr]
  simp

/-- The standard Boolean Bernoulli law has the expected real-parameter masses. -/
theorem bernoulli_true_mass (p : unitInterval) :
    ProbabilityTheory.bernoulliMeasure true false p {true} =
      ENNReal.ofReal (p : ℝ) := by
  rw [ProbabilityTheory.bernoulliMeasure_apply_of_mem_of_notMem p
    (measurableSet_singleton true) (by simp) (by simp)]
  exact (ENNReal.ofReal_eq_coe_nnreal p.property.1).symm

theorem bernoulli_false_mass (p : unitInterval) :
    ProbabilityTheory.bernoulliMeasure true false p {false} =
      ENNReal.ofReal (1 - (p : ℝ)) := by
  rw [ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_mem p
    (measurableSet_singleton false) (by simp) (by simp)]
  exact (ENNReal.ofReal_eq_coe_nnreal (sub_nonneg.mpr p.property.2)).symm

/-- Bernoulli specialization with exactly the `ofReal p` density budget. -/
theorem expected_density_bernoulli
    {A : Type u_A} {K : Type u_K} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
    (P : Measure A) [IsProbabilityMeasure P] (p : unitInterval)
    (addr : A → ℝ → K) (haddr : ∀ a, Measurable (addr a)) :
    (∫⁻ z, volume (selectedSet addr z ∩ Set.Icc (0 : ℝ) 1)
      ∂(P.prod (Measure.pi (fun _ : K =>
        ProbabilityTheory.bernoulliMeasure true false p)))) = ENNReal.ofReal (p : ℝ) := by
  rw [expected_density_selectedSet P _ addr haddr, bernoulli_true_mass]

end Problem310.RandomSetDensity

end

end OAI
