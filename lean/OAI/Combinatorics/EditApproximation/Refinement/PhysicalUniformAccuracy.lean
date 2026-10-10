import OAI.Combinatorics.EditApproximation.Refinement.PhysicalFamilyRuntime
import OAI.Combinatorics.EditApproximation.Geometry.AccuracyPrefixInspection
import OAI.Combinatorics.EditApproximation.Geometry.AccuracyCutoff
import OAI.Combinatorics.EditApproximation.Probability.ExactSuffixDP
import OAI.Combinatorics.EditApproximation.Refinement.ComputedSourceAddressBits
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

open MeasureTheory ProbabilityTheory Filter

/-- Every test is on a bounded word prefix or on the computed input
parameters. Rejected inputs use the exact suffix dynamic program. -/




 theorem physicalLargeInput_eventually (epsilon : BinaryFraction) (hepsilon : 0 < epsilon.value) :
    ∀ᶠ N in atTop, physicalLargeInput N epsilon := by
  filter_upwards [inspectAccuracy_eventually_accepts epsilon,
    eventually_ge_atTop (accuracyCutoff epsilon.value), computed_localOnlineMassBound_word] with N hi hc hw
  exact ⟨by rw [hi]; rfl, accuracyCutoff_sufficient N epsilon.value hepsilon hc, hw⟩

section Uniform

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P T S H B : ℕ)
  [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
  (depth : PhysicalEntry M J target.length → ℕ)

local notation "passes" => computedSeedPassCount N
local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)
local notation "Table" => ChargedPhysicalRequest M J target.length (passes + 1) (H ^ 2) T S

abbrev PhysicalUniformOutcome := Unit ⊕ PhysicalFamilyRuntimeOutcome (M := M) (J := J) (R := R)
  target N P H

instance physicalUniformOutcome_measurableSingleton :
    MeasurableSingletonClass (PhysicalUniformOutcome (M := M) (J := J) (R := R) target N P H) := by
  refine ⟨fun outcome => ?_⟩
  exact measurableSet_sum_iff.mpr
    ⟨(Set.to_countable _).measurableSet, (Set.to_countable _).measurableSet⟩

noncomputable def physicalUniformLaw (epsilon : BinaryFraction) :
    Measure (PhysicalUniformOutcome (M := M) (J := J) (R := R) target N P H) :=
  if physicalLargeInput N epsilon then
    (physicalFamilyRuntimeLaw (R := R) target N P H
      (physicalCoarseSeedLaw source target N B depth)).map Sum.inr
  else Measure.dirac (Sum.inl ())

instance physicalUniformLaw_probability (epsilon : BinaryFraction) :
    IsProbabilityMeasure (physicalUniformLaw (R := R) source target N P H B depth epsilon) := by
  classical
  unfold physicalUniformLaw
  split <;> infer_instance

noncomputable def physicalUniformAnswer (hH : 0 < H) (bits : ℕ)
    (encode : Sum Key Table → ℕ)
    (outcome : PhysicalUniformOutcome (M := M) (J := J) (R := R) target N P H) : ℕ :=
  match outcome with
  | .inl _ => exactSuffixAnswer source target
  | .inr execution => physicalFamilyRuntimeAnswer source target N P T S H hH bits encode
      (finalTargetState target.length) execution

 theorem physicalUniformAnswer_equal (hH : 0 < H) (bits : ℕ) (encode : Sum Key Table → ℕ)
    (heq : source = target)
    (outcome : PhysicalUniformOutcome (M := M) (J := J) (R := R) target N P H) :
    physicalUniformAnswer source target N P T S H hH bits encode outcome = 0 := by
  cases outcome with
  | inl unitValue => exact exactSuffixAnswer_equal source target heq
  | inr execution =>
    unfold physicalUniformAnswer physicalFamilyRuntimeAnswer physicalFamilyMemoAnswer
    have htarget : source = substring target (finalTargetState target.length).lo
        (finalTargetState target.length).hi := by simpa [finalTargetState, substring] using heq
    dsimp only
    rw [ite_eq_left htarget]

/-- Uniform correctness of the memo evaluator driven by rejection trials,
under finite Bernstein bounds for coarse and group coordinates. -/
theorem physical_uniform_conditional_accuracy (epsilon : BinaryFraction) (hH : 0 < H) (bits : ℕ)
    (encode : Sum Key Table → ℕ)
    (hcode : physicalLargeInput N epsilon → Function.Injective encode)
    (hfits : physicalLargeInput N epsilon → ∀ key, encode key < 2 ^ bits)
    (hsize : source.length + target.length ≤ N)
    (hMeq : M = (integerParameters N).M) (hJeq : J = intervalTreeDepth M source.length)
    (hPeq : P = (integerParameters N).P) (hTeq : T = (integerParameters N).T)
    (hSeq : S = (integerParameters N).S) (hHeq : H = inputHeight N)
    (hB : B = (integerParameters N).B)
    (hdepth : ∀ state, depth state = computedCoarseDepth N
      (coarseEntryWidth (physicalSource source state.1) (substring target state.2.lo state.2.hi)))
    (coarseBernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin B =>
      (PMF.uniformOfFintype (Fin B)).toMeasure))
    (groupBernstein : ∀ b : ℕ, ∀ h : Fin (groupDyadicScales M b ell).length,
      FiniteBernsteinInput (Measure.pi fun _ : Fin
        (groupSampleCount M (ell ^ 80) b (groupDyadicScaleAt M b ell h)) =>
        (PMF.uniformOfFintype (Fin M)).toMeasure))
    (hepsilon : 0 < epsilon.value) :
    (2 / 3 : ℝ) ≤ (physicalUniformLaw (R := R) source target N P H B depth epsilon).real
      {outcome | EditDistortion.edit source target ≤
        physicalUniformAnswer source target N P T S H hH bits encode outcome ∧
        (physicalUniformAnswer source target N P T S H hH bits encode outcome : ℝ) ≤
          (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target} := by
  classical
  by_cases hlarge : physicalLargeInput N epsilon
  · have hN := largeAccuracyInput_pos N epsilon.value hlarge.2.1
    have hreal := largeAccuracyInput_real N epsilon.value hlarge.2.1
    have hepsilonR : (0 : ℝ) < epsilon.value := by exact_mod_cast hepsilon
    have hPpos : 0 < P := by
      rw [hPeq]
      exact Nat.pow_pos (Nat.two_pow_pos _)
    rw [physicalUniformLaw, ite_eq_left hlarge,
      map_measureReal_apply (by fun_prop) (Set.to_countable _).measurableSet]
    change (2 / 3 : ℝ) ≤ (physicalFamilyRuntimeLaw (R := R) target N P H
      (physicalCoarseSeedLaw source target N B depth)).real
      {execution | EditDistortion.edit source target ≤
        physicalFamilyRuntimeAnswer source target N P T S H hH bits encode
          (finalTargetState target.length) execution ∧
        (physicalFamilyRuntimeAnswer source target N P T S H hH bits encode
          (finalTargetState target.length) execution : ℝ) ≤
          (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target}
    have hevent := physicalFamilyRuntimeAnswer_event source target N P T S H hPpos hH bits encode
      (hcode hlarge) (hfits hlarge) (physicalCoarseSeedLaw source target N B depth)
      (finalTargetState target.length)
      {answer | EditDistortion.edit source target ≤ answer ∧
        (answer : ℝ) ≤ (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target}
    simp only [Set.mem_ofPred_eq] at hevent
    rw [hevent]
    exact local_physical_conditional_accuracy source target N P T S H B depth hN hreal.1
      hsize hMeq hJeq hPeq hTeq hSeq hHeq hB hdepth coarseBernstein groupBernstein
      (epsilon.value : ℝ) hepsilonR hreal.2
  · rw [physicalUniformLaw, ite_eq_right hlarge]
    have hgood : (Sum.inl () : PhysicalUniformOutcome (M := M) (J := J) (R := R) target N P H) ∈
        {outcome | EditDistortion.edit source target ≤
          physicalUniformAnswer source target N P T S H hH bits encode outcome ∧
          (physicalUniformAnswer source target N P T S H hH bits encode outcome : ℝ) ≤
            (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target} :=
      exactSuffixAnswer_approximation source target epsilon.value (by exact_mod_cast hepsilon.le)
    rw [Measure.real, Measure.dirac_apply_of_mem hgood, ENNReal.toReal_one]
    norm_num

end Uniform

end EditApproximation

end OAI
