import OAI.NumberTheory.CubicMoment.Estimates.LowCommonRow
import OAI.NumberTheory.CubicMoment.Estimates.LowCommonScale
import OAI.NumberTheory.CubicMoment.Estimates.HeightGramContinuity

namespace OAI
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment.ProfileControl

theorem low_common_block_height_log_saving
    (hpnt : PrimaryPrimePNT) (j : ℕ)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ (P : PoissonProfileBudget) (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z A T M u : ℝ) (k : Eisenstein), (65536:ℝ)^2 ≤ Z → Z^(3/2:ℝ) ≤ A →
      (1+Real.log Z)^Ct ≤ T → 0 ≤ M → primary k → Squarefree k →
      norm k ≤ Z^(1/2:ℝ) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      dyadicHeightMean (fun t => ‖commonGramBlock S
        (fun b => star (dispersionAmplitude β (u+t) b)) P.V A k‖) T ≤
      (K*P.cost)*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^j*
        ((2:ℝ)^(primaryPrimeFactors k).card*norm k^(-(5/3:ℝ))) := by
  obtain ⟨K₀,Ct,hK₀,hrow₀⟩ := low_common_row_height hpnt j hMV hC hHuxley
  refine ⟨K₀*(2:ℝ)^j,Ct,by positivity,?_⟩
  intro P S β Z A T M u k hZlarge hA hT hM hk hsk hkZ hS hβ
  have hZ : 0 < Z := by nlinarith
  have hZ1 : 1 ≤ Z := by nlinarith
  obtain ⟨hfloor,hlarge⟩ := low_common_floor_large hZlarge
    (norm_pos_of_ne_zero (primary_ne_zero hk)) hkZ
  let K := K₀*P.cost
  have hK : 0 < K := mul_pos hK₀ P.cost_pos
  have hrow := hrow₀ P
  have hA₀ : 0 < A := (Real.rpow_pos_of_pos hZ _).trans_le hA
  have hT₀ : 0 < T := (pow_pos (by linarith [Real.log_nonneg hZ1]) _).trans_le hT
  have hS₀ : ∀ b ∈ S, primary b ∧ Squarefree b := fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩
  let Fset := (primaryPrimeFactors k).powerset
  let F (s : Finset Eisenstein) (t : ℝ) :=
    coprimeGramForm (residualRows S k)
      (commonBlockCoefficient (fun b => star (dispersionAmplitude β (u+t) b)) k (∏ p ∈ s,p))
      P.V (A/norm (∏ p ∈ s,p))
  have hfc (s : Finset Eisenstein) : Continuous (F s) := by
    have he (t : ℝ) := common_coprime_height_eq S β k (∏ p ∈ s,p) hk hS₀ (u+t) P.V
      (A/norm (∏ p ∈ s,p))
    simp_rw [F,he]
    exact (continuous_coprimeDispersionGram _ _ P.V _).comp
      (show Continuous (fun t : ℝ => u+t) from continuous_const.add continuous_id)
  have he (t : ℝ) : commonGramBlock S
      (fun b => star (dispersionAmplitude β (u+t) b)) P.V A k =
      ∑ s ∈ Fset, (idealMoebius (∏ p ∈ s,p):ℂ)*F s t :=
    commonGramBlock_moebius S hS₀ _ P.V P.compact P.smooth hA₀ hk hsk
  simp_rw [he]
  apply (dyadicHeightMean_norm_sum_le Fset
    (fun s t => (idealMoebius (∏ p ∈ s,p):ℂ)*F s t)
    (fun s _ => continuous_const.mul (hfc s)) hT₀).trans
  have hb (s : Finset Eisenstein) (hs : s ∈ Fset) :
      dyadicHeightMean (fun t => ‖(idealMoebius (∏ p ∈ s,p):ℂ)*F s t‖) T ≤
        K*(2:ℝ)^j*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)*norm k^(-(5/3:ℝ))/(1+Real.log Z)^j := by
    have hsub : s ⊆ primaryPrimeFactors k := Finset.mem_powerset.mp hs
    have hm : primary (∏ p ∈ s,p) := primary_finset_prod _ _
      (fun p hp => (primaryPrimeFactor_spec hk (hsub hp)).1.1)
    have hmk : (∏ p ∈ s,p) ∣ k := (primary_subsets_prod_dvd hk hsub k).mpr
      (fun p hp => (primaryPrimeFactor_spec hk (hsub hp)).2)
    have hmc : Continuous (fun t => (idealMoebius (∏ p ∈ s,p):ℂ)*F s t) :=
      continuous_const.mul (hfc s)
    have havg := dyadicHeightMean_mono
      (f := fun t => ‖(idealMoebius (∏ p ∈ s,p):ℂ)*F s t‖)
      (g := fun t => ‖F s t‖) hmc.norm (hfc s).norm hT₀ (fun t _ => by
        rw [norm_mul]
        exact mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_idealMoebius_le_one _))
    apply havg.trans
    have hh := hrow S β Z A T M u k _ hZ.le hA hT hM hk hm hmk hfloor hlarge hS hβ
    apply hh.trans
    have hscale := low_common_residual_scale j
      (show 0 ≤ A from (Real.rpow_nonneg hZ.le _).trans hA) hZ1
      (norm_pos_of_ne_zero (primary_ne_zero hk)) (one_le_norm (primary_ne_zero hm)) hkZ
    have hb := mul_le_mul_of_nonneg_left hscale
      (show 0 ≤ K*M^2 by positivity)
    convert hb using 1 <;> ring
  exact (Finset.sum_le_sum hb).trans_eq (by
    simp only [Fset,Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    dsimp [K]
    ring)


end CubicFirstMoment.ProfileControl

end

end OAI
