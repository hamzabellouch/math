import OAI.NumberTheory.CubicMoment.Estimates.PrimeGroupTailCommonRow
import OAI.NumberTheory.CubicMoment.Estimates.HeightGramContinuity

namespace OAI

/-! Restore every Möbius divisor in a small common-factor block. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem primeGroupTail_common_block_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z A T u : ℝ) (k : Eisenstein), 0 < Z → Z^(27/25:ℝ) ≤ A →
      Z^(1/50:ℝ) ≤ T → primary k → Squarefree k →
      4 ≤ (⌊Z/norm k⌋₊:ℝ) → 16 ≤ (⌊Z/norm k⌋₊:ℝ)^(3/4:ℝ) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      dyadicHeightMean (fun t => ‖commonGramBlock S
        (fun b => star (dispersionAmplitude β (u+t) b)) V A k‖) T ≤
      K*A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ)*
        ((2:ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S β k) := by
  obtain ⟨K,hK,hrow⟩ := primeGroupTail_common_row_height_power hMV hC hHuxley V hV hV'
  refine ⟨K,hK,?_⟩
  intro S β Z A T u k hZ hA hT hk hsk hfloor hlarge hS
  have hA₀ : 0 < A := (Real.rpow_pos_of_pos hZ _).trans_le hA
  have hT₀ : 0 < T := (Real.rpow_pos_of_pos hZ _).trans_le hT
  have hS₀ : ∀ b ∈ S, primary b ∧ Squarefree b := fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩
  let P := (primaryPrimeFactors k).powerset
  let F (s : Finset Eisenstein) (t : ℝ) :=
    coprimeGramForm (residualRows S k)
      (commonBlockCoefficient (fun b => star (dispersionAmplitude β (u+t) b)) k (∏ p ∈ s,p))
      V (A/norm (∏ p ∈ s,p))
  have hfc (s : Finset Eisenstein) : Continuous (F s) := by
    have he (t : ℝ) := common_coprime_height_eq S β k (∏ p ∈ s,p) hk hS₀ (u+t) V
      (A/norm (∏ p ∈ s,p))
    simp_rw [F,he]
    exact (continuous_coprimeDispersionGram _ _ V _).comp
      (show Continuous (fun t : ℝ => u+t) from continuous_const.add continuous_id)
  have he (t : ℝ) : commonGramBlock S
      (fun b => star (dispersionAmplitude β (u+t) b)) V A k =
      ∑ s ∈ P, (idealMoebius (∏ p ∈ s,p):ℂ)*F s t :=
    commonGramBlock_moebius S hS₀ _ V hV hV' hA₀ hk hsk
  simp_rw [he]
  apply (dyadicHeightMean_norm_sum_le P
    (fun s t => (idealMoebius (∏ p ∈ s,p):ℂ)*F s t)
    (fun s _ => continuous_const.mul (hfc s)) hT₀).trans
  have hb (s : Finset Eisenstein) (hs : s ∈ P) :
      dyadicHeightMean (fun t => ‖(idealMoebius (∏ p ∈ s,p):ℂ)*F s t‖) T ≤
        K*A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ)*commonBlockEnergy S β k := by
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
    exact havg.trans (hrow S β Z A T u k _ hZ.le hA hT hk
      hm
      hmk hfloor hlarge hS)
  exact (Finset.sum_le_sum hb).trans_eq (by
    simp only [P,Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    ring)

end CubicFirstMoment

end

end OAI
