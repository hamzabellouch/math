import OAI.Combinatorics.Progressions.Fourier.PrincipalCoefficientResidueSpectrum

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {B : Type*} [Fintype B] [DecidableEq B]
  {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
  (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
  (a : (∀ b, IntegerScalarCubeBox Empty (c b).length) → ℂ)
  (J : Finset (Finset I)) (offset : B → ℤ) (shift : J → ℤ)

noncomputable def correlatedModeratePointMass (z : J → ℤ) : ℂ :=
  (weightedModerateIntegerProductSource c s).complexMean (fun x =>
    if weightedModerateIntegerJetSum c s J offset shift x = z then a (fun b => (x b).1) else 0)

theorem correlatedModeratePointMass_zero_off (z : J → ℤ)
    (hz : ∃ S : J, weightedModerateJetBound c s offset S < |z S - shift S|) :
    correlatedModeratePointMass c s a J offset shift z = 0 := by
  obtain ⟨S, hS⟩ := hz
  have he (x : ∀ b, IntegerScalarCubeBox Empty (c b).length ×
      (∀ j, IntegerScalarCubeBox I (s b j).length)) :
      weightedModerateIntegerJetSum c s J offset shift x ≠ z := by
    intro h
    have hb := weightedModerateIntegerJetSum_bound c s J offset shift x S
    rw [h] at hb
    exact (not_lt_of_ge hb) hS
  simp only [correlatedModeratePointMass, he, ite_false,
    FiniteProbabilityWeights.complexMean_const]

theorem correlatedModeratePointMass_eq_residue (z : J → ℤ) (M : ℕ)
    (Z : J → ℤ) (hM : ∀ S : J, weightedModerateJetBound c s offset S + Z S < (M : ℤ))
    (hz : ∀ S : J, |z S - shift S| ≤ Z S) :
    correlatedModeratePointMass c s a J offset shift z =
      (weightedModerateIntegerProductSource c s).complexMean (fun x =>
        if integerGridResidue M (weightedModerateIntegerJetSum c s J offset shift x) =
          integerGridResidue M z then a (fun b => (x b).1) else 0) := by
  apply FiniteProbabilityWeights.complexMean_congr_support
  intro x _
  have he := integerGridResidue_eq_iff_of_close M
    (weightedModerateIntegerJetSum c s J offset shift x) z (fun S => ?_)
  · simp only [he]
  · have hy := abs_le.mp (weightedModerateIntegerJetSum_bound c s J offset shift x S)
    have hz' := abs_le.mp (hz S)
    have hM' := hM S
    rw [abs_lt]
    constructor <;> omega

theorem correlatedModeratePointMass_norm_le (ha : ∀ z, ‖a z‖ ≤ 1) (z : J → ℤ) :
    ‖correlatedModeratePointMass c s a J offset shift z‖ ≤
      finiteImageMass (weightedModerateIntegerProductSource c s)
        (weightedModerateIntegerJetSum c s J offset shift) z := by
  apply (FiniteProbabilityWeights.norm_complexMean_le_mean_norm _ _).trans
  apply FiniteProbabilityWeights.mean_mono
  intro x
  by_cases hx : weightedModerateIntegerJetSum c s J offset shift x = z
  · simp only [hx, ite_true]
    exact ha _
  · simp only [hx, ite_false, norm_zero, le_refl]

end Erdos3

end

end OAI
