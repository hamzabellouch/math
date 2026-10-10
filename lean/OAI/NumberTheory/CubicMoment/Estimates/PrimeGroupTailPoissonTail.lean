import OAI.NumberTheory.CubicMoment.Estimates.SmallBPoissonEnvelope
import OAI.NumberTheory.CubicMoment.Estimates.PrimeGroupTailPoissonCutoff

namespace OAI

/-! The high-frequency estimate improves as the outer length grows.
Retaining its inverse powers removes the artificial upper bound on A. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma primeGroupTail_unbounded_tail_scale {Z A J : ℝ} (hZ : 1 ≤ Z)
    (hA : Z^(27/25:ℝ) ≤ A) (hJ : Z^(19/20:ℝ)/32 ≤ J) :
    let t := A/(27*Z^2)
    A*Z*t^(-3:ℝ)/(t*J)^240 ≤ (864:ℝ)^243*Z^(-2:ℝ) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have ha : 0 < A := (Real.rpow_pos_of_pos hz _).trans_le hA
  let t := A/(27*Z^2)
  change A*Z*t^(-3:ℝ)/(t*J)^240 ≤ _
  have ht : 0 < t := by dsimp [t]; positivity
  have hj : 0 < J := (div_pos (Real.rpow_pos_of_pos hz _) (by norm_num)).trans_le hJ
  have hcut : Z^(3/100:ℝ)/864 ≤ t*J := (primeGroupTail_poisson_cutoff_scale hZ hA hJ).2
  have ha2 : Z^2 ≤ A^2 := by
    apply pow_le_pow_left₀ hz.le
    exact (show Z ≤ Z^(27/25:ℝ) by
      nth_rw 1 [← Real.rpow_one Z]
      exact Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)).trans hA
  have hfirst : A*Z*t^(-3:ℝ) ≤ (864:ℝ)^3*Z^5 := by
    have he : A*Z*t^(-3:ℝ) = (27:ℝ)^3*Z^7/A^2 := by
      rw [Real.rpow_neg ht.le,Real.rpow_ofNat]
      dsimp [t]
      field_simp
    rw [he]
    apply (div_le_iff₀ (sq_pos_of_pos ha)).mpr
    have hm := mul_le_mul_of_nonneg_left ha2 (show 0 ≤ (27:ℝ)^3*Z^5 by positivity)
    have hc : (27:ℝ)^3*Z^5*A^2 ≤ (864:ℝ)^3*Z^5*A^2 := by gcongr; norm_num
    apply (le_trans ?_ hm).trans hc
    ring_nf
    rfl
  have hinv : (t*J)⁻¹ ≤ 864/Z^(3/100:ℝ) := by
    rw [← one_div,div_le_iff₀ (mul_pos ht hj),div_mul_eq_mul_div]
    have hh := (div_le_iff₀ (by norm_num : (0:ℝ) < 864)).mp hcut
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hz _)).mpr
    nlinarith
  have hpower : ((t*J)^240)⁻¹ ≤ (864:ℝ)^240*Z^(-36/5:ℝ) := by
    rw [← inv_pow]
    apply (pow_le_pow_left₀ (by positivity) hinv 240).trans_eq
    rw [div_pow,← Real.rpow_mul_natCast hz.le]
    rw [show (3/100:ℝ)*(240:ℕ) = 36/5 by norm_num,
      show (-36/5:ℝ) = -(36/5) by ring,Real.rpow_neg hz.le,div_eq_mul_inv]
  calc
    _ ≤ ((864:ℝ)^3*Z^5)*((864:ℝ)^240*Z^(-36/5:ℝ)) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul hfirst hpower (by positivity) (by positivity)
    _ = (864:ℝ)^243*Z^(-11/5:ℝ) := by
      have he : Z^5*Z^(-36/5:ℝ) = Z^(-11/5:ℝ) := by
        rw [← Real.rpow_natCast Z 5,← Real.rpow_add hz]
        norm_num
      calc
        _ = ((864:ℝ)^3*864^240)*(Z^5*Z^(-36/5:ℝ)) := by ring
        _ = ((864:ℝ)^3*864^240)*Z^(-11/5:ℝ) := by rw [he]
        _ = _ := by rw [←pow_add]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)) (by positivity)

theorem primeGroupTail_poisson_tail_power (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (H : ℕ → Finset Eisenstein)
      (β : Eisenstein → ℂ) (A N Z u : ℝ) (n : ℕ),
      1 ≤ N → N ≤ Z → Z^(27/25:ℝ) ≤ A → Z^(19/20:ℝ)/32 ≤ (2:ℝ)^n →
      (∀ a ∈ S, primary a ∧ N ≤ norm a ∧ norm a ≤ Z) →
      (∀ j, H j ⊆ frequencyDyad j) →
      Summable (fun j => finitePoissonContribution S (H (j+n)) β u V A) ∧
      ‖∑' j : ℕ, finitePoissonContribution S (H (j+n)) β u V A‖ ≤
        K*Z^(-2:ℝ)*∑ a ∈ S, ‖β a‖^2 := by
  obtain ⟨K,hK,hbound⟩ := arbitrary_poisson_energy_tail V hV hV' 240
  refine ⟨2*K*(864:ℝ)^243,by positivity,?_⟩
  intro S H β A N Z u n hN hNZ hAlo hcut hS hH
  have hZ : 1 ≤ Z := hN.trans hNZ
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hA : 0 < A := (Real.rpow_pos_of_pos hZp _).trans_le hAlo
  let t := A/(27*Z^2)
  have ht : 0 < t := by dsimp [t]; positivity
  have hb := hbound S H β A N Z u n hA hNp hNZ hS hH
  refine ⟨hb.1,?_⟩
  have hp := primeGroupTail_unbounded_tail_scale hZ hAlo hcut
  have hgeo : ((2:ℝ)^(-2:ℝ))^n*(1-(2:ℝ)^(-2:ℝ))⁻¹ ≤ 2 := by
    norm_num
    have hh : (1/4:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  calc
    _ ≤ (K*(A/N)*Z*(∑ a ∈ S, ‖β a‖^2)/(t*(2:ℝ)^n)^240)*(t^(-3:ℝ)*2) :=
      hb.2.trans (mul_le_mul_of_nonneg_left
        (by nlinarith [mul_le_mul_of_nonneg_left hgeo (Real.rpow_nonneg ht.le (-3))])
        (by positivity))
    _ = (2*K/N)*(∑ a ∈ S, ‖β a‖^2)*(A*Z*t^(-3:ℝ)/(t*(2:ℝ)^n)^240) := by ring
    _ ≤ (2*K/N)*(∑ a ∈ S, ‖β a‖^2)*((864:ℝ)^243*Z^(-2:ℝ)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ (2*K)*(∑ a ∈ S, ‖β a‖^2)*((864:ℝ)^243*Z^(-2:ℝ)) := by
      gcongr
      exact div_le_self (by positivity) hN
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
