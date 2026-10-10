import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorEnvelope
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedPoissonTail

namespace OAI

/-! The full high-frequency tail at the stopped cutoff, retaining the
explicit polynomial cost of the small square divisor. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma stopped_divisor_tail_scale {Z A J D : ℝ} (hZ : 1 ≤ Z) (hD : 0 < D)
    (hA : Z^(3/2:ℝ) ≤ A) (hJ : Z^(3/5:ℝ)/4 ≤ J) :
    let t := A/(27*D^3*Z^2)
    (A/D^2)*Z*t^(-3:ℝ)/(t*J)^80 ≤ (108:ℝ)^83*D^247*Z^(-2:ℝ) := by
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hAp : 0 < A := (Real.rpow_pos_of_pos hZp _).trans_le hA
  have hJp : 0 < J := (div_pos (Real.rpow_pos_of_pos hZp _) (by norm_num)).trans_le hJ
  let t := A/(27*D^3*Z^2)
  let t₀ := A/(27*Z^2)
  have ht : 0 < t := by dsimp [t]; positivity
  have ht₀ : 0 < t₀ := by dsimp [t₀]; positivity
  change (A/D^2)*Z*t^(-3:ℝ)/(t*J)^80 ≤ _
  have he : (A/D^2)*Z*t^(-3:ℝ)/(t*J)^80 =
      D^247*(A*Z*t₀^(-3:ℝ)/(t₀*J)^80) := by
    rw [Real.rpow_neg ht.le,Real.rpow_ofNat,Real.rpow_neg ht₀.le,Real.rpow_ofNat]
    dsimp [t,t₀]
    field_simp
  rw [he]
  exact (mul_le_mul_of_nonneg_left (stopped_poisson_tail_scale hZ hA hJ)
    (pow_nonneg hD.le _)).trans_eq (by ring)

theorem stopped_divisor_poisson_tail_power (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (H : ℕ → Finset Eisenstein)
      (β : Eisenstein → ℂ) (A N Z u : ℝ) (n : ℕ) (d : Eisenstein) (hd : d ≠ 0),
      1 ≤ N → N ≤ Z → Z^(3/2:ℝ) ≤ A → Z^(3/5:ℝ)/4 ≤ (2:ℝ)^n →
      (∀ a ∈ S, primary a ∧ N ≤ norm a ∧ norm a ≤ Z) →
      (∀ j, H j ⊆ divisorFrequencyDyad d hd j) →
      Summable (fun j => finiteDivisorPoissonContribution d S (H (j+n)) β u V A) ∧
      ‖∑' j : ℕ, finiteDivisorPoissonContribution d S (H (j+n)) β u V A‖ ≤
        K*(norm d)^247*Z^(-2:ℝ)*∑ a ∈ S, ‖β a‖^2 := by
  obtain ⟨K,hK,hbound⟩ := arbitrary_divisor_poisson_energy_tail V hV hV' 80
  refine ⟨2*K*(108:ℝ)^83,by positivity,?_⟩
  intro S H β A N Z u n d hd hN hNZ hAlo hcut hS hH
  have hZ : 1 ≤ Z := hN.trans hNZ
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hdN : 0 < norm d := norm_pos_of_ne_zero hd
  have hA : 0 < A := (Real.rpow_pos_of_pos hZp _).trans_le hAlo
  let t := A/(27*(norm d)^3*Z^2)
  have ht : 0 < t := by dsimp [t]; positivity
  have hb := hbound S H β A N Z u n d hd hA hNp hNZ hS hH
  refine ⟨hb.1,?_⟩
  have hp := stopped_divisor_tail_scale hZ hdN hAlo hcut
  have hgeo : ((2:ℝ)^(-2:ℝ))^n*(1-(2:ℝ)^(-2:ℝ))⁻¹ ≤ 2 := by
    norm_num
    have hh : (1/4:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  calc
    _ ≤ (K*((A/(norm d)^2)/N)*Z*(∑ a ∈ S, ‖β a‖^2)/(t*(2:ℝ)^n)^80)*
        (t^(-3:ℝ)*2) := hb.2.trans (mul_le_mul_of_nonneg_left
      (by nlinarith [mul_le_mul_of_nonneg_left hgeo (Real.rpow_nonneg ht.le (-3))])
      (by positivity))
    _ = (2*K/N)*(∑ a ∈ S, ‖β a‖^2)*
        ((A/(norm d)^2)*Z*t^(-3:ℝ)/(t*(2:ℝ)^n)^80) := by ring
    _ ≤ (2*K/N)*(∑ a ∈ S, ‖β a‖^2)*((108:ℝ)^83*(norm d)^247*Z^(-2:ℝ)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ (2*K)*(∑ a ∈ S, ‖β a‖^2)*((108:ℝ)^83*(norm d)^247*Z^(-2:ℝ)) := by
      gcongr
      exact div_le_self (by positivity) hN
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
