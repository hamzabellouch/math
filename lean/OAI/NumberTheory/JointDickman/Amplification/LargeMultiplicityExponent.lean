import OAI.NumberTheory.JointDickman.Amplification.LargeAdditionAvailability
import OAI.NumberTheory.JointDickman.Amplification.OmissionEnvelope
import OAI.NumberTheory.JointDickman.Amplification.RegularPrefixChoices

namespace OAI

/-! # The combined entropy exponent in large representation classes -/

namespace JointDickman

noncomputable def largeMultiplicityBase : ℝ := 2*Real.log 2-1-weightBaseExponent

noncomputable def largeMultiplicityLoss (Δ δ τ ε : ℝ) : ℝ :=
  3*Δ+2*δ+(Real.log 2-Real.log (2*δ))*τ+5*ε+2*highOmissionExponent τ

theorem largeMultiplicityBase_bounds : 0 < largeMultiplicityBase ∧
    largeMultiplicityBase < (233/1000 : ℝ) := by
  unfold largeMultiplicityBase weightBaseExponent
  constructor <;> linarith [Real.log_two_lt_d9,Real.log_two_gt_d9]

/-- One old-coefficient choice at each endpoint and the opposite remainder's
addition choices account for all three combinatorial entropy factors. -/
theorem large_multiplicity_exponent_bound {g Δ δ τ ε ℓ : ℝ} {d f : ℕ}
    (hg : 0 ≤ g) (hg1 : g ≤ 1) (hδ : 0 ≤ δ) :
    largeAvailabilityExponent g Δ δ τ ε ℓ d+
      ((g/2)*Real.binEntropy (2*min ((d : ℝ)/(g*ℓ)) (1/2))+ε+highOmissionExponent τ)+
      ((g/2)*Real.binEntropy (2*min ((f : ℝ)/(g*ℓ)) (1/2))+ε+highOmissionExponent τ)+
      ((g/2)*Real.binEntropy (2*min ((f : ℝ)/(g*ℓ)) (1/2))+ε) ≤
        largeMultiplicityBase+largeMultiplicityLoss Δ δ τ ε := by
  have hd := Real.binEntropy_le_log_two (p := 2*min ((d : ℝ)/(g*ℓ)) (1/2))
  have hf := Real.binEntropy_le_log_two (p := 2*min ((f : ℝ)/(g*ℓ)) (1/2))
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hd hf) hg
  have hb := mul_le_mul_of_nonneg_right hg1 largeMultiplicityBase_bounds.1.le
  have hδg := mul_le_mul_of_nonneg_right hg1 hδ
  unfold largeAvailabilityExponent largeMultiplicityBase largeMultiplicityLoss at *
  nlinarith

end JointDickman

end OAI
