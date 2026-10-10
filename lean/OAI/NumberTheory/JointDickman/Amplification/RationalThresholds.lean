import OAI.NumberTheory.JointDickman.Arithmetic.RationalBinSmooth

namespace OAI

/-! # Exact common-denominator thresholds for the rational fixed-scale law -/
namespace JointDickman
open Filter
open scoped Topology

theorem rational_threshold_fraction {c : ℚ} (hc : 0 < c) (hc1 : c < 1) :
    0 < c.num.toNat ∧ c.num.toNat < c.den ∧
      (c : ℝ) = (c.num.toNat : ℝ)/(c.den : ℝ) := by
  have hp : 0 < c.num := Rat.num_pos.mpr hc
  have hn : (c.num.toNat : ℝ) = (c.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hp.le
  have he : (c : ℝ) = (c.num.toNat : ℝ)/(c.den : ℝ) := by rw [Rat.cast_def,hn]
  have hd : (0 : ℝ) < c.den := by exact_mod_cast c.den_pos
  have hlt : (c.num.toNat : ℝ) < c.den := by
    apply (div_lt_one hd).mp
    rw [← he]
    exact_mod_cast hc1
  exact ⟨by omega,by exact_mod_cast hlt,he⟩

theorem rational_common_denominator {c d : ℚ}
    (hc : 0 < c) (hc1 : c < 1) (hd : 0 < d) (hd1 : d < 1) :
    ∃ J k l : ℕ, 2 ≤ J ∧ 0 < k ∧ k < J ∧ 0 < l ∧ l < J ∧
      (c : ℝ) = (k : ℝ)/J ∧ (d : ℝ) = (l : ℝ)/J := by
  obtain ⟨hcpos,hclt,hce⟩ := rational_threshold_fraction hc hc1
  obtain ⟨hdpos,hdlt,hde⟩ := rational_threshold_fraction hd hd1
  refine ⟨c.den*d.den,c.num.toNat*d.den,d.num.toNat*c.den,?_,
    Nat.mul_pos hcpos d.den_pos,Nat.mul_lt_mul_of_pos_right hclt d.den_pos,
    Nat.mul_pos hdpos c.den_pos,?_,?_,?_⟩
  · have hcd : 2 ≤ c.den := by omega
    have hdd : 1 ≤ d.den := d.den_pos
    nlinarith
  · simpa only [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right hdlt c.den_pos
  · rw [hce]
    push_cast
    have hdn : (d.den : ℝ) ≠ 0 := by exact_mod_cast d.den_ne_zero
    field_simp
  · rw [hde]
    push_cast
    have hcn : (c.den : ℝ) ≠ 0 := by exact_mod_cast c.den_ne_zero
    have hdn : (d.den : ℝ) ≠ 0 := by exact_mod_cast d.den_ne_zero
    field_simp

theorem rationalFixedScaleLaw_of_distance_divergence
    (hMR : PublishedInputs.RealShortIntervalInput) (hMRT : PublishedInputs.ComplexShortIntervalInput)
    (hKMT : CharacterDistanceDivergence) (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput) (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) (hMP : PublishedInputs.PrimeProductMertensInput)
    (hMC : ∀ B M : ℕ, PublishedInputs.FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
    (hBill : PublishedInputs.FiniteBinDistributionInput) : RationalFixedScaleLaw := by
  intro c d hc hc1 hd hd1
  obtain ⟨J,k,l,hJ,hk,hkj,hl,hlj,hce,hde⟩ := rational_common_denominator hc hc1 hd hd1
  rw [hce,hde]
  exact fixedDensity_common_denominator hMR hMRT hKMT hFord hSD hSW hM hMP hMC hBill hJ hk hkj hl hlj

theorem rationalFixedScaleLaw_of_published
    (hMR : PublishedInputs.RealShortIntervalInput) (hMRT : PublishedInputs.ComplexShortIntervalInput)
    (hKMT : PublishedInputs.CharacterDistanceInput) (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput) (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) (hMP : PublishedInputs.PrimeProductMertensInput)
    (_hMV : PublishedInputs.MultiplicativeExponentialInput)
    (hMC : ∀ B M : ℕ, PublishedInputs.FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
    (hBill : PublishedInputs.FiniteBinDistributionInput) : RationalFixedScaleLaw :=
  rationalFixedScaleLaw_of_distance_divergence hMR hMRT
    (characterDistanceDivergence_of_published hKMT) hFord hSD hSW hM hMP hMC hBill

end JointDickman

end OAI
