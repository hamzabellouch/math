import OAI.NumberTheory.CubicMoment.Decomposition.StoppedBoundedTotal
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCommonCoefficient
import OAI.NumberTheory.CubicMoment.Estimates.SmallBCommonScale

namespace OAI

/-! Pointwise control of the actual shortened common-factor row.  The
bounded coefficient, not an assumed quotient cancellation property, is
used after the exact normalized Gauss reparametrization. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma bounded_common_residual_scale {A Z r m : ℝ} (d : ℕ)
    (hA : 0 ≤ A) (hZ : 0 ≤ Z) (hr : 1 ≤ r) (hm : 1 ≤ m)
    (hres : 1 ≤ Z/r) :
    (A/m)^(2/3:ℝ)*(Z/r)^(5/3:ℝ)*(1+Real.log (Z/r))^d ≤
      A^(2/3:ℝ)*Z^(5/3:ℝ)*r^(-(5/3:ℝ))*(1+Real.log Z)^d := by
  have hrp : 0 < r := zero_lt_one.trans_le hr
  have hresp : 0 < Z/r := zero_lt_one.trans_le hres
  have houter : (A/m)^(2/3:ℝ) ≤ A^(2/3:ℝ) :=
    Real.rpow_le_rpow (div_nonneg hA (by linarith)) (div_le_self hA hm) (by norm_num)
  have hlog : (1+Real.log (Z/r))^d ≤ (1+Real.log Z)^d :=
    pow_le_pow_left₀ (by linarith [Real.log_nonneg hres])
      (by linarith [Real.log_le_log hresp (div_le_self hZ hr)]) d
  have hquot : (Z/r)^(5/3:ℝ) = Z^(5/3:ℝ)*r^(-(5/3:ℝ)) := by
    rw [Real.div_rpow hZ hrp.le,Real.rpow_neg hrp.le,div_eq_mul_inv]
  calc
    _ ≤ (A^(2/3:ℝ)*(Z/r)^(5/3:ℝ))*(1+Real.log Z)^d :=
      mul_le_mul (mul_le_mul_of_nonneg_right houter (by positivity)) hlog
        (pow_nonneg (by linarith [Real.log_nonneg hres]) _) (by positivity)
    _ = _ := by rw [hquot]; ring

theorem bounded_common_coprime_row_at_scale (hpnt : PrimaryPrimePNT)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (S : Finset Eisenstein)
      (β : Eisenstein → ℂ) (Z A M u : ℝ) (k m : Eisenstein),
      0 ≤ M → primary k → primary m → 65536 ≤ Z/norm k →
      (Z/norm k)^(3/2:ℝ) ≤ A/norm m →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ Z/2 ≤ norm a ∧ norm a ≤ Z) →
      (∀ a ∈ S, ‖β a‖ ≤ M) →
      ‖coprimeGramForm (residualRows S k)
        (commonBlockCoefficient (fun a => star (dispersionAmplitude β u a)) k m)
        V (A/norm m)‖ ≤
      K*(A/norm m)^(2/3:ℝ)*(Z/norm k)^(5/3:ℝ)*M^2*(1+Real.log (Z/norm k))^d := by
  obtain ⟨K,d,hK,hbound⟩ := bounded_coprime_dispersion hpnt hHuxley V hV hV'
  refine ⟨K,d,hK,?_⟩
  intro S β Z A M u k m hM hk _hm hres hA hS hβ
  have hk₀ := primary_ne_zero hk
  have hS₀ : ∀ a ∈ S, primary a ∧ Squarefree a := fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩
  have hr := residualRows_primary hk hS₀
  let v := commonBlockCoefficient (fun a => star (β a*gauss a)) k m
  have hrows : ∀ a ∈ residualRows S k,
      primary a ∧ Squarefree a ∧ (Z/norm k)/2 ≤ norm a ∧ norm a ≤ Z/norm k := by
    intro a ha
    have hka := hS (k*a) ((mem_residualRows hk₀).mp ha)
    refine ⟨(hr a ha).1,(hr a ha).2,?_,?_⟩
    · rw [div_right_comm]
      apply (div_le_iff₀ (norm_pos_of_ne_zero hk₀)).mpr
      rw [norm_mul_eq] at hka
      nlinarith [hka.2.2.1]
    · apply (le_div_iff₀ (norm_pos_of_ne_zero hk₀)).mpr
      simpa only [norm_mul_eq,mul_comm] using hka.2.2.2
  have hv : ∀ a ∈ residualRows S k, ‖gramUntwist v a‖ ≤ M := by
    intro a ha
    rw [gramUntwist_norm (hr a ha).1 (hr a ha).2]
    apply (commonBlockCoefficient_norm_le _ k m (hr a ha).1).trans
    change ‖star (β (k*a)*gauss (k*a))‖ ≤ M
    rw [norm_star,norm_mul]
    exact (mul_le_of_le_one_right (_root_.norm_nonneg _)
      (norm_gauss_le_one (hS (k*a) ((mem_residualRows hk₀).mp ha)).1)).trans
      (hβ (k*a) ((mem_residualRows hk₀).mp ha))
  rw [common_coprime_height_eq S β k m hk hS₀]
  exact hbound (residualRows S k) (gramUntwist v) (Z/norm k) M (A/norm m) u
    hres hM hA hrows hv

theorem bounded_common_coprime_row (hpnt : PrimaryPrimePNT)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (S : Finset Eisenstein)
      (β : Eisenstein → ℂ) (Z A M u : ℝ) (k m : Eisenstein),
      0 ≤ Z → Z^(3/2:ℝ) ≤ A → 0 ≤ M → primary k → primary m → m ∣ k →
      65536 ≤ Z/norm k →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ Z/2 ≤ norm a ∧ norm a ≤ Z) →
      (∀ a ∈ S, ‖β a‖ ≤ M) →
      ‖coprimeGramForm (residualRows S k)
        (commonBlockCoefficient (fun a => star (dispersionAmplitude β u a)) k m)
        V (A/norm m)‖ ≤
      K*(A/norm m)^(2/3:ℝ)*(Z/norm k)^(5/3:ℝ)*M^2*(1+Real.log (Z/norm k))^d := by
  obtain ⟨K,d,hK,hrow⟩ := bounded_common_coprime_row_at_scale hpnt hHuxley V hV hV'
  refine ⟨K,d,hK,?_⟩
  intro S β Z A M u k m hZ hA hM hk hm hmk hres hS hβ
  exact hrow S β Z A M u k m hM hk hm hres
    (smallB_common_outer_scale hZ (one_le_norm (primary_ne_zero hk))
      (norm_pos_of_ne_zero (primary_ne_zero hm)) (norm_le_of_dvd (primary_ne_zero hk) hmk) hA)
    hS hβ

end CubicFirstMoment

end

end OAI
