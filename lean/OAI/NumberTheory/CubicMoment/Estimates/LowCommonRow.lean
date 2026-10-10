import OAI.NumberTheory.CubicMoment.Estimates.LowCoprimeReal
import OAI.NumberTheory.CubicMoment.Estimates.SmallBCommonRow

namespace OAI
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment.ProfileControl

theorem low_common_row_height (hpnt : PrimaryPrimePNT) (j : ℕ)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ (P : PoissonProfileBudget) (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z A T M u : ℝ) (k m : Eisenstein), 0 ≤ Z → Z^(3/2:ℝ) ≤ A →
      (1+Real.log Z)^Ct ≤ T → 0 ≤ M → primary k → primary m → m ∣ k →
      65536 ≤ (⌊Z/norm k⌋₊:ℝ) → 16 ≤ (⌊Z/norm k⌋₊:ℝ)^(3/4:ℝ) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      dyadicHeightMean (fun t => ‖coprimeGramForm (residualRows S k)
        (commonBlockCoefficient (fun b => star (dispersionAmplitude β (u+t) b)) k m)
        P.V (A/norm m)‖) T ≤
      (K*P.cost)*M^2*(A/norm m)^(2/3:ℝ)*(Z/norm k)^(5/3:ℝ)/
        (1+Real.log (Z/norm k))^j := by
  obtain ⟨K₀,Ct,hK₀,hbound₀⟩ := low_coprime_height_real hpnt j hMV hC hHuxley
  refine ⟨K₀,Ct,hK₀,?_⟩
  intro P S β Z A T M u k m hZ hA hT hM hk hm hmk hfloor hlarge hS hβ
  let K := K₀*P.cost
  have hK : 0 < K := mul_pos hK₀ P.cost_pos
  have hbound := hbound₀ P
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
  have hres0 : 0 ≤ Z/norm k := div_nonneg hZ (zero_le_one.trans hk₁)
  have hresp : 0 < Z/norm k := by
    have hf := Nat.floor_le hres0
    linarith
  have hres1 : 1 ≤ Z/norm k := by
    have hf := Nat.floor_le hres0
    linarith
  have hTrow : (1+Real.log (Z/norm k))^Ct ≤ T := by
    apply le_trans _ hT
    apply pow_le_pow_left₀ (by linarith [Real.log_nonneg hres1])
    linarith [Real.log_le_log hresp (div_le_self hZ hk₁)]
  have hv : ∀ b ∈ residualRows S k, ‖v b‖ ≤ M := by
    intro b hb
    have hkb := hS (k*b) ((mem_residualRows hk₀).mp hb)
    apply (commonBlockCoefficient_norm_le _ k m (hr b hb).1).trans
    change ‖star (β (k*b)*gauss (k*b))‖ ≤ M
    rw [norm_star,norm_mul]
    exact (mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_gauss_le_one hkb.1)).trans
      (hβ (k*b) ((mem_residualRows hk₀).mp hb))
  have hrow := hbound (residualRows S k) v (Z/norm k) (A/norm m) T M u
    hfloor hlarge hM hTrow
    (smallB_common_outer_scale hZ hk₁ (norm_pos_of_ne_zero hm₀) hmkN hA) hrows hv
  have he (t : ℝ) : coprimeGramForm (residualRows S k)
      (commonBlockCoefficient (fun b => star (dispersionAmplitude β (u+t) b)) k m) P.V (A/norm m) =
      coprimeGramForm (residualRows S k) (fun b => v b*star (normTwist (u+t) b)) P.V (A/norm m) := by
    rw [common_coprime_height_eq S β k m hk hS₀,
      ← coprimeGramForm_height_eq _ hr]
  simp_rw [he]
  exact hrow


end CubicFirstMoment.ProfileControl

end

end OAI
