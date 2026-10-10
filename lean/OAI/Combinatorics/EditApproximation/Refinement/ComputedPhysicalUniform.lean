import OAI.Combinatorics.EditApproximation.Refinement.PhysicalUniformAccuracy
import OAI.Combinatorics.EditApproximation.Refinement.ComputedFamilyMemoCode
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

theorem two_hundred_le_two_pow_thousand : 200 ≤ (2 : ℕ) ^ 1000 := by
  have h := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by decide : 8 ≤ 1000)
  exact le_trans (by decide : 200 ≤ (2 : ℕ) ^ 8) h

open MeasureTheory ProbabilityTheory

theorem computedParameterP_pos (N : ℕ) : 0 < (integerParameters N).P :=
  Nat.pow_pos (Nat.two_pow_pos _)









abbrev ComputedPhysicalOutcome (source target : List ℕ) (N : ℕ) :=
  PhysicalUniformOutcome (M := (integerParameters N).M)
    (J := intervalTreeDepth (integerParameters N).M source.length) (R := inputHeight N ^ 2)
    target N (integerParameters N).P (inputHeight N)

noncomputable def computedPhysicalLaw (source target : List ℕ) (N : ℕ) (epsilon : BinaryFraction) :
    Measure (ComputedPhysicalOutcome source target N) :=
  physicalUniformLaw (R := inputHeight N ^ 2) source target N (integerParameters N).P
    (inputHeight N) (integerParameters N).B (computedPhysicalCoarseDepth source target N) epsilon

noncomputable def computedPhysicalAnswer (source target : List ℕ) (N : ℕ)
    (outcome : ComputedPhysicalOutcome source target N) : ℕ :=
  physicalUniformAnswer source target N (integerParameters N).P (integerParameters N).T
    (integerParameters N).S (inputHeight N) (Nat.two_pow_pos _)
    (16384 * inputHeight N + 5) (computedFamilyMemoCode source target N (inputHeight N ^ 2)) outcome

 theorem computedPhysicalAnswer_equal (source target : List ℕ) (N : ℕ) (heq : source = target)
    (outcome : ComputedPhysicalOutcome source target N) : computedPhysicalAnswer source target N outcome = 0 :=
  physicalUniformAnswer_equal source target N (integerParameters N).P (integerParameters N).T
    (integerParameters N).S (inputHeight N) (Nat.two_pow_pos _) _ _ heq outcome

 theorem computed_physical_uniform_conditional_accuracy (source target : List ℕ) (N : ℕ)
    (epsilon : BinaryFraction) (hepsilon : 0 < epsilon.value)
    (hsize : source.length + target.length ≤ N)
    (coarseBernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin (integerParameters N).B =>
      (PMF.uniformOfFintype (Fin (integerParameters N).B)).toMeasure))
    (groupBernstein : ∀ b : ℕ, ∀ h : Fin
      (groupDyadicScales (integerParameters N).M b (inputSmallLog N)).length,
      FiniteBernsteinInput (Measure.pi fun _ : Fin
        (groupSampleCount (integerParameters N).M (inputSmallLog N ^ 80) b
          (groupDyadicScaleAt (integerParameters N).M b (inputSmallLog N) h)) =>
        (PMF.uniformOfFintype (Fin (integerParameters N).M)).toMeasure)) :
    (2 / 3 : ℝ) ≤ (computedPhysicalLaw source target N epsilon).real
      {outcome | EditDistortion.edit source target ≤ computedPhysicalAnswer source target N outcome ∧
        (computedPhysicalAnswer source target N outcome : ℝ) ≤
          (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target} := by
  apply physical_uniform_conditional_accuracy source target N (integerParameters N).P
    (integerParameters N).T (integerParameters N).S (inputHeight N) (integerParameters N).B
    (computedPhysicalCoarseDepth source target N) epsilon (Nat.two_pow_pos _)
    (16384 * inputHeight N + 5) (computedFamilyMemoCode source target N (inputHeight N ^ 2))
    ?_ ?_ hsize rfl rfl rfl rfl rfl rfl rfl (fun _ => rfl) coarseBernstein groupBernstein hepsilon
  · intro hlarge
    exact computedFamilyMemoCode_injective source target N (inputHeight N ^ 2)
      (largeAccuracyInput_pos N epsilon.value hlarge.2.1) (by
        have h := hlarge.2.1.1
        have hc := two_hundred_le_two_pow_thousand
        omega)
  · intro hlarge key
    exact computedFamilyMemoCode_fits source target N (inputHeight N ^ 2)
      (largeAccuracyInput_pos N epsilon.value hlarge.2.1) hlarge.2.1.1 hsize le_rfl hlarge.2.2 key

end EditApproximation

end OAI
