import OAI.NumberTheory.CubicMoment.Estimates.SmallBPoissonEnvelope
import OAI.NumberTheory.CubicMoment.Estimates.PoissonTailPower

namespace OAI

/-! Absolute control after the stopped-row frequency cutoff b^(3/5).
At A≥b^(3/2) this is a positive power beyond the natural Poisson scale;
the inverse powers of A make the bound valid without an upper A limit. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma stopped_poisson_cutoff {Z : ℝ} (_hZ : 0 < Z) (hlarge : 2 ≤ Z^(3/5:ℝ)) :
    ∃ n : ℕ, Z^(3/5:ℝ)/4 ≤ (2:ℝ)^n ∧
      ∀ j : ℕ, j < n → 2*(2:ℝ)^j ≤ Z^(3/5:ℝ) := by
  obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near
    ((le_div_iff₀ (by norm_num : (0:ℝ) < 2)).mpr (by simpa using hlarge))
    (by norm_num : (1:ℝ) < 2)
  refine ⟨n,?_,?_⟩
  · have hh := (div_lt_iff₀ (by norm_num : (0:ℝ) < 2)).mp hn'
    rw [pow_succ] at hh
    linarith
  · intro j hj
    have hp : (2:ℝ)^j ≤ (2:ℝ)^n := pow_le_pow_right₀ (by norm_num) hj.le
    have hn := (le_div_iff₀ (by norm_num : (0:ℝ) < 2)).mp hn
    nlinarith

lemma stopped_poisson_cutoff_scale {Z A J : ℝ} (hZ : 1 ≤ Z)
    (hA : Z^(3/2:ℝ) ≤ A) (hJ : Z^(3/5:ℝ)/4 ≤ J) :
    1/(108*Z^2) ≤ A/(27*Z^2) ∧
      Z^(1/10:ℝ)/108 ≤ (A/(27*Z^2))*J := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have ha : 1 ≤ A := (Real.one_le_rpow hZ (by norm_num)).trans hA
  constructor
  · apply (div_le_div_iff₀ (by positivity : (0:ℝ) < 108*Z^2)
      (by positivity : (0:ℝ) < 27*Z^2)).mpr
    nlinarith [sq_pos_of_pos hz]
  · have hmul := mul_le_mul hA hJ (by positivity : 0 ≤ Z^(3/5:ℝ)/4)
      (zero_le_one.trans ha)
    have hid : Z^(3/2:ℝ)*Z^(3/5:ℝ) = Z^(1/10:ℝ)*Z^2 := by
      rw [← Real.rpow_natCast Z 2,← Real.rpow_add hz,← Real.rpow_add hz]
      norm_num
    have hp : Z^(1/10:ℝ)*Z^2 ≤ 4*(A*J) := by
      rw [← mul_div_assoc,hid] at hmul
      linarith
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 108)).mpr
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hz)).mp
    calc
      _ = Z^(1/10:ℝ)*Z^2 := mul_comm _ _
      _ ≤ 4*(A*J) := hp
      _ = Z^2*((A/(27*Z^2))*J*108) := by field_simp; ring

lemma stopped_poisson_tail_scale {Z A J : ℝ} (hZ : 1 ≤ Z)
    (hA : Z^(3/2:ℝ) ≤ A) (hJ : Z^(3/5:ℝ)/4 ≤ J) :
    let t := A/(27*Z^2)
    A*Z*t^(-3:ℝ)/(t*J)^80 ≤ (108:ℝ)^83*Z^(-2:ℝ) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have ha : 0 < A := (Real.rpow_pos_of_pos hz _).trans_le hA
  let t := A/(27*Z^2)
  change A*Z*t^(-3:ℝ)/(t*J)^80 ≤ _
  have ht : 0 < t := by dsimp [t]; positivity
  have hj : 0 < J := (div_pos (Real.rpow_pos_of_pos hz _) (by norm_num)).trans_le hJ
  have hcut : Z^(1/10:ℝ)/108 ≤ t*J := (stopped_poisson_cutoff_scale hZ hA hJ).2
  have ha2 : Z^3 ≤ A^2 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hz.le (3/2:ℝ)) hA 2
    have he : (Z^(3/2:ℝ))^2 = Z^3 := by
      rw [← Real.rpow_mul_natCast hz.le]
      norm_num
    rwa [he] at hh
  have hfirst : A*Z*t^(-3:ℝ) ≤ (108:ℝ)^3*Z^4 := by
    have he : A*Z*t^(-3:ℝ) = (27:ℝ)^3*Z^7/A^2 := by
      rw [Real.rpow_neg ht.le,Real.rpow_ofNat]
      dsimp [t]
      field_simp
    rw [he]
    apply (div_le_iff₀ (sq_pos_of_pos ha)).mpr
    have hm := mul_le_mul_of_nonneg_left ha2 (show 0 ≤ (27:ℝ)^3*Z^4 by positivity)
    have hc : (27:ℝ)^3*Z^4*A^2 ≤ (108:ℝ)^3*Z^4*A^2 := by gcongr; norm_num
    apply (le_trans ?_ hm).trans hc
    ring_nf
    rfl
  have hinv : (t*J)⁻¹ ≤ 108/Z^(1/10:ℝ) := by
    rw [← one_div,div_le_iff₀ (mul_pos ht hj),div_mul_eq_mul_div]
    have hh := (div_le_iff₀ (by norm_num : (0:ℝ) < 108)).mp hcut
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hz _)).mpr
    nlinarith
  have hpower : ((t*J)^80)⁻¹ ≤ (108:ℝ)^80*Z^(-8:ℝ) := by
    rw [← inv_pow]
    apply (pow_le_pow_left₀ (by positivity) hinv 80).trans_eq
    rw [div_pow,← Real.rpow_mul_natCast hz.le]
    norm_num
    simp only [div_eq_mul_inv]
  calc
    _ ≤ ((108:ℝ)^3*Z^4)*((108:ℝ)^80*Z^(-8:ℝ)) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul hfirst hpower (by positivity) (by positivity)
    _ = (108:ℝ)^83*Z^(-4:ℝ) := by
      have he : Z^4*Z^(-8:ℝ) = Z^(-4:ℝ) := by
        rw [← Real.rpow_natCast Z 4,← Real.rpow_add hz]
        norm_num
      rw [show (108:ℝ)^83 = 108^3*108^80 by ring]
      nlinarith only [he]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)) (by positivity)

theorem stopped_poisson_tail_power (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (H : ℕ → Finset Eisenstein)
      (β : Eisenstein → ℂ) (A N Z u : ℝ) (n : ℕ),
      1 ≤ N → N ≤ Z → Z^(3/2:ℝ) ≤ A → Z^(3/5:ℝ)/4 ≤ (2:ℝ)^n →
      (∀ a ∈ S, primary a ∧ N ≤ norm a ∧ norm a ≤ Z) →
      (∀ j, H j ⊆ frequencyDyad j) →
      Summable (fun j => finitePoissonContribution S (H (j+n)) β u V A) ∧
      ‖∑' j : ℕ, finitePoissonContribution S (H (j+n)) β u V A‖ ≤
        K*Z^(-2:ℝ)*∑ a ∈ S, ‖β a‖^2 := by
  obtain ⟨K,hK,hbound⟩ := arbitrary_poisson_energy_tail V hV hV' 80
  refine ⟨2*K*(108:ℝ)^83,by positivity,?_⟩
  intro S H β A N Z u n hN hNZ hAlo hcut hS hH
  have hZ : 1 ≤ Z := hN.trans hNZ
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hA : 0 < A := (Real.rpow_pos_of_pos hZp _).trans_le hAlo
  let t := A/(27*Z^2)
  have ht : 0 < t := by dsimp [t]; positivity
  have hb := hbound S H β A N Z u n hA hNp hNZ hS hH
  refine ⟨hb.1,?_⟩
  have hp := stopped_poisson_tail_scale hZ hAlo hcut
  have hgeo : ((2:ℝ)^(-2:ℝ))^n*(1-(2:ℝ)^(-2:ℝ))⁻¹ ≤ 2 := by
    norm_num
    have hh : (1/4:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  calc
    _ ≤ (K*(A/N)*Z*(∑ a ∈ S, ‖β a‖^2)/(t*(2:ℝ)^n)^80)*(t^(-3:ℝ)*2) :=
      hb.2.trans (mul_le_mul_of_nonneg_left
        (by nlinarith [mul_le_mul_of_nonneg_left hgeo (Real.rpow_nonneg ht.le (-3))])
        (by positivity))
    _ = (2*K/N)*(∑ a ∈ S, ‖β a‖^2)*(A*Z*t^(-3:ℝ)/(t*(2:ℝ)^n)^80) := by ring
    _ ≤ (2*K/N)*(∑ a ∈ S, ‖β a‖^2)*((108:ℝ)^83*Z^(-2:ℝ)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ (2*K)*(∑ a ∈ S, ‖β a‖^2)*((108:ℝ)^83*Z^(-2:ℝ)) := by
      gcongr
      exact div_le_self (by positivity) hN
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
