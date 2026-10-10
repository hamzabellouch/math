import OAI.NumberTheory.PrimePackets.ObservationRefinement

namespace OAI

/-!
# Entropy-rate comparison from one-step conditional entropy

The finite-block estimate here is the approximation step needed when
replacing finite observations by successively finer geometric partitions.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace PrimeDegreePackets

variable {Y α β : Type*} [MeasurableSpace Y]

lemma observationEntropy_unique [Fintype α] [Unique α]
    (μ : Measure Y) [IsProbabilityMeasure μ] (P : Y → α) :
    observationEntropy μ P = 0 := by
  have hP : P = fun _ => default := funext (fun y => Subsingleton.elim _ _)
  rw [hP]
  simp [observationEntropy, finiteShannon]

omit [MeasurableSpace Y] in
lemma orbitName_one (T : Y → Y) (P : Y → α) :
    orbitName T P 1 = fun y (_ : Fin 1) => P y := by
  funext y j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  rfl

lemma conditionalOrbitEntropy_one [Fintype α] [Fintype β]
    (μ : Measure Y) (T : Y → Y) (P : Y → α) (Q : Y → β) :
    conditionalObservationEntropy μ (orbitName T P 1) (orbitName T Q 1) =
      conditionalObservationEntropy μ P Q := by
  rw [orbitName_one, orbitName_one]
  exact conditionalObservationEntropy_injective μ P Q
    (fun a (_ : Fin 1) => a) (fun b (_ : Fin 1) => b)
    (fun _ _ h => congrFun h 0) (fun _ _ h => congrFun h 0)

theorem conditionalOrbitEntropy_le [Fintype α] [Fintype β]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) (N : ℕ) :
    conditionalObservationEntropy μ (orbitName T P N) (orbitName T Q N) ≤
      (N : ℝ) * conditionalObservationEntropy μ P Q := by
  induction N with
  | zero =>
      let : Unique ((Fin 0 → β) × (Fin 0 → α)) :=
        uniqueOfSubsingleton (default, default)
      unfold conditionalObservationEntropy
      rw [observationEntropy_unique, observationEntropy_unique]
      simp
  | succ N ih =>
      have hPN := orbitName_measurable_fiber hT.measurable hP N
      have hQN := orbitName_measurable_fiber hT.measurable hQ N
      have hP1 := orbitName_measurable_fiber hT.measurable hP 1
      have hQ1 := orbitName_measurable_fiber hT.measurable hQ 1
      have heq :
          conditionalObservationEntropy μ (orbitName T P (N+1)) (orbitName T Q (N+1)) =
          conditionalObservationEntropy μ
            (fun y => (orbitName T P N y, orbitName T P 1 (T^[N] y)))
            (fun y => (orbitName T Q N y, orbitName T Q 1 (T^[N] y))) := by
        rw [orbitName_add T P N 1, orbitName_add T Q N 1]
        exact conditionalObservationEntropy_injective μ _ _
          (Fin.appendEquiv N 1) (Fin.appendEquiv N 1)
          (Fin.appendEquiv N 1).injective (Fin.appendEquiv N 1).injective
      rw [heq]
      have H := conditionalObservationEntropy_pair_pair_le μ
        (orbitName T P N) (fun y => orbitName T P 1 (T^[N] y))
        (orbitName T Q N) (fun y => orbitName T Q 1 (T^[N] y))
        hPN (fun a => (hP1 a).preimage (hT.measurable.iterate N))
        hQN (fun b => (hQ1 b).preimage (hT.measurable.iterate N))
      rw [conditionalObservationEntropy_comp_preserving μ _ _ hP1 hQ1 (hT.iterate N),
        conditionalOrbitEntropy_one] at H
      refine H.trans ?_
      have H' := add_le_add ih (le_refl (conditionalObservationEntropy μ P Q))
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using H'

/-- A finite observation approximates entropy rates up to its one-step
conditional entropy. This is the standard finite-partition approximation bound. -/
theorem observationEntropyRate_le_add_conditional [Fintype α] [Fintype β]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) :
    observationEntropyRate μ T P ≤
      observationEntropyRate μ T Q + conditionalObservationEntropy μ P Q := by
  have H : ∀ᶠ N : ℕ in atTop,
      observationEntropy μ (orbitName T P N) / (N : ℝ) ≤
      observationEntropy μ (orbitName T Q N) / (N : ℝ) +
        conditionalObservationEntropy μ P Q := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have H₁ := observationEntropy_le_add_conditional μ
      (orbitName T P N) (orbitName T Q N)
      (orbitName_measurable_fiber hT.measurable hP N)
      (orbitName_measurable_fiber hT.measurable hQ N)
    have H₂ := conditionalOrbitEntropy_le μ hT P Q hP hQ N
    calc
      _ ≤ (observationEntropy μ (orbitName T Q N) +
          (N : ℝ) * conditionalObservationEntropy μ P Q) / (N : ℝ) :=
        div_le_div_of_nonneg_right (H₁.trans (add_le_add le_rfl H₂)) (Nat.cast_nonneg N)
      _ = _ := by rw [add_div]; congr 1; field_simp
  exact le_of_tendsto_of_tendsto (tendsto_observationEntropyRate μ hT P hP)
    ((tendsto_observationEntropyRate μ hT Q hQ).add tendsto_const_nhds) H

end PrimeDegreePackets

end

end OAI
