import OAI.NumberTheory.CubicMoment.Estimates.PrimeGroupTailCommonScale

namespace OAI

/-! The actual Möbius summand of a shared-factor row inherits the
arbitrary-coefficient height saving, with the original row energy. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem primeGroupTail_common_row_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z A T u : ℝ) (k m : Eisenstein), 0 ≤ Z → Z^(27/25:ℝ) ≤ A →
      Z^(1/50:ℝ) ≤ T → primary k → primary m → m ∣ k →
      4 ≤ (⌊Z/norm k⌋₊:ℝ) → 16 ≤ (⌊Z/norm k⌋₊:ℝ)^(3/4:ℝ) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      dyadicHeightMean (fun t => ‖coprimeGramForm (residualRows S k)
        (commonBlockCoefficient (fun b => star (dispersionAmplitude β (u+t) b)) k m)
        V (A/norm m)‖) T ≤
      K*A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ)*commonBlockEnergy S β k := by
  obtain ⟨K,hK,hbound⟩ := primeGroupTail_coprime_height_real hMV hC hHuxley V hV hV'
  refine ⟨K,hK,?_⟩
  intro S β Z A T u k m hZ hA hT hk hm hmk hfloor hlarge hS
  have hk₀ := primary_ne_zero hk
  have hk₁ := one_le_norm hk₀
  have hm₀ := primary_ne_zero hm
  have hm₁ := one_le_norm hm₀
  have hmkN := norm_le_of_dvd hk₀ hmk
  have hS₀ : ∀ b ∈ S, primary b ∧ Squarefree b := fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩
  have hr := residualRows_primary hk hS₀
  let v := commonBlockCoefficient (fun b => star (β b*gauss b)) k m
  have hrows : ∀ b ∈ residualRows S k,
      primary b ∧ Squarefree b ∧ (Z/norm k)/2 ≤ norm b ∧ norm b ≤ Z/norm k := by
    intro b hb
    have hkb := hS (k*b) ((mem_residualRows hk₀).mp hb)
    refine ⟨(hr b hb).1,(hr b hb).2,?_,?_⟩
    · rw [div_right_comm]
      apply (div_le_iff₀ (norm_pos_of_ne_zero hk₀)).mpr
      rw [norm_mul_eq] at hkb
      nlinarith [hkb.2.2.1]
    · apply (le_div_iff₀ (norm_pos_of_ne_zero hk₀)).mpr
      simpa only [norm_mul_eq,mul_comm] using hkb.2.2.2
  have hrow := hbound (residualRows S k) v (Z/norm k) (A/norm m) T u hfloor hlarge
    (primeGroupTail_common_height_scale hZ hk₁ hT)
    (primeGroupTail_common_outer_scale hZ hk₁ (norm_pos_of_ne_zero hm₀) hmkN hA) hrows
  have he (t : ℝ) : coprimeGramForm (residualRows S k)
      (commonBlockCoefficient (fun b => star (dispersionAmplitude β (u+t) b)) k m) V (A/norm m) =
      coprimeGramForm (residualRows S k) (fun b => v b*star (normTwist (u+t) b)) V (A/norm m) := by
    rw [common_coprime_height_eq S β k m hk hS₀,
      ← coprimeGramForm_height_eq _ hr]
  simp_rw [he]
  have henergy : (∑ b ∈ residualRows S k, ‖v b‖^2) ≤ commonBlockEnergy S β k := by
    apply (commonBlockCoefficient_unweighted_energy_le S hS₀
      (fun b => star (β b*gauss b)) hk m).trans
    unfold commonBlockEnergy
    apply Finset.sum_le_sum
    intro b hb
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hkb := (hS (k*b) ((mem_residualRows hk₀).mp hb)).1
    apply pow_le_pow_left₀ (by positivity)
    simp only [norm_star,norm_mul]
    exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_gauss_le_one hkb)
  have hA₀ : 0 ≤ A := (Real.rpow_nonneg hZ _).trans hA
  exact hrow.trans (by
    have hs := primeGroupTail_common_bound_scale hZ hA₀ hk₁ hm₁
    calc
      _ ≤ K*(A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ))*(∑ b ∈ residualRows S k, ‖v b‖^2) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs hK.le) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      _ ≤ _ := by
        have hsc : 0 ≤ K*A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ) := by positivity
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left henergy hsc)

end CubicFirstMoment

end

end OAI
