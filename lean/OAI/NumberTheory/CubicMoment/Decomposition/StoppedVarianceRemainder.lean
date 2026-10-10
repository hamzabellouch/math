import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCommonRemainder

namespace OAI

/-! Exact restoration of the noncoprime part of a square-divisor variance.
The bound uses active roughness of the original coefficient, which is
preserved by the actual cubic divisor twist. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem bounded_rough_divisor_variance_remainder (hpnt : PrimaryPrimePNT)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ (K : ℝ) (j : ℕ), 0 < K ∧ ∀ (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z A M u R : ℝ) (d : Eisenstein), 2 < Z → Z^(3/2:ℝ) ≤ A →
      0 ≤ M → 0 < R → primary d → norm d ≤ Z^(1/1000:ℝ) → (norm d)^4 ≤ R →
      65536*(Z/2)^(1/4:ℝ) ≤ Z →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ Z/2 ≤ norm a ∧ norm a ≤ Z) →
      (∀ a ∈ S, ‖β a‖ ≤ M) →
      (∀ a ∈ S, β a ≠ 0 → ∀ p, primaryPrime p → p ∣ a → R ≤ norm p) →
      ‖divisorDispersionVariance d S β u V A-divisorCoprimeDispersionGram d S β u V A‖ ≤
      K*(A^(2/3:ℝ)*Z^(5/3:ℝ)*(1+Real.log Z)^j*R^(-(1/6:ℝ))+
        A^(2/3:ℝ)*Z^(5/3-1/32:ℝ)+A*Z)*M^2 := by
  obtain ⟨K,j,hK,hbound⟩ := bounded_rough_common_remainder hpnt hHuxley V hV hV'
  refine ⟨K,j,hK,?_⟩
  intro S β Z A M u R d hZ hA hM hR hd hdhi hdR hcut hS hβ hrough
  have hAp : 0 < A := (Real.rpow_pos_of_pos (by linarith : 0 < Z) _).trans_le hA
  have hβ' : ∀ a ∈ S, ‖divisorTwistedCoefficient d β a‖ ≤ M := by
    intro a ha
    simp only [divisorTwistedCoefficient,norm_mul,norm_star]
    exact (mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one
      (hS a ha).1 _)).trans (hβ a ha)
  have hr' : ∀ a ∈ S, divisorTwistedCoefficient d β a ≠ 0 →
      ∀ p, primaryPrime p → p ∣ a → R ≤ norm p := by
    intro a ha hne
    apply hrough a ha
    intro hz
    exact hne (by simp only [divisorTwistedCoefficient,hz,zero_mul])
  rw [divisorVariance_sub_coprime_common hd S
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩) β u V hV hV' hAp]
  exact hbound S (divisorTwistedCoefficient d β) Z A M u R (norm d) hZ hA hM hR
    (one_le_norm (primary_ne_zero hd)) hdhi hdR hcut hS hβ' hr'

end CubicFirstMoment

end

end OAI
