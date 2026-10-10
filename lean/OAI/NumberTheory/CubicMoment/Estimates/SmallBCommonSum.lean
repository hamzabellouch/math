import OAI.NumberTheory.CubicMoment.Estimates.SmallBCommonBlock

namespace OAI

/-! Sum the actual small-common-factor blocks with their joint divisor
energy. The loss is smaller than the height saving. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma continuous_commonGramBlock_height (S : Finset Eisenstein)
    (β : Eisenstein → ℂ) (k : Eisenstein) (V : ℝ → ℂ) (A u : ℝ) :
    Continuous (fun t => commonGramBlock S
      (fun b => star (dispersionAmplitude β (u+t) b)) V A k) := by
  unfold commonGramBlock
  apply continuous_finsetSum
  intro a ha
  apply continuous_finsetSum
  intro b hb
  split_ifs
  · exact ((((continuous_dispersionAmplitude β (k*a)).comp
      (continuous_const.add continuous_id)).star).mul
      ((((continuous_dispersionAmplitude β (k*b)).comp
      (continuous_const.add continuous_id)).star).star)).mul continuous_const
  · exact continuous_const

theorem smallB_common_sum_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S I : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z A T u : ℝ), 0 < Z → Z^(3/2:ℝ) ≤ A → Z^(1/50:ℝ) ≤ T →
      I ⊆ commonRowFactors S →
      (∀ k ∈ I, 4 ≤ (⌊Z/norm k⌋₊:ℝ) ∧ 16 ≤ (⌊Z/norm k⌋₊:ℝ)^(3/4:ℝ)) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      dyadicHeightMean (fun t => ‖∑ k ∈ I, commonGramBlock S
        (fun b => star (dispersionAmplitude β (u+t) b)) V A k‖) T ≤
      K*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨K,hK,hblock⟩ := smallB_common_block_height_power hMV hC hHuxley V hV hV'
  obtain ⟨E,hE,henergy⟩ := common_energy_small_power (1/80000) (by norm_num)
  refine ⟨K*E,by positivity,?_⟩
  intro S I β Z A T u hZ hA hT hI hfloor hS
  have hS₀ : ∀ b ∈ S, primary b ∧ Squarefree b := fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩
  have hA₀ : 0 < A := (Real.rpow_pos_of_pos hZ _).trans_le hA
  have hT₀ : 0 < T := (Real.rpow_pos_of_pos hZ _).trans_le hT
  have hsum := dyadicHeightMean_norm_sum_le I
    (fun k t => commonGramBlock S (fun b => star (dispersionAmplitude β (u+t) b)) V A k)
    (fun k _ => continuous_commonGramBlock_height S β k V A u) hT₀
  have hb (k : Eisenstein) (hk : k ∈ I) := hblock S β Z A T u k hZ hA hT
    (commonRowFactors_spec hS₀ (hI hk)).1 (commonRowFactors_spec hS₀ (hI hk)).2
    (hfloor k hk).1 (hfloor k hk).2 hS
  have hbound : (∑ k ∈ I, (2:ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S β k) ≤
      E*Z^(1/80000:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
    apply le_trans _ (henergy S β Z (fun b hb => ⟨(hS b hb).1,(hS b hb).2.1,(hS b hb).2.2.2⟩))
    exact Finset.sum_le_sum_of_subset_of_nonneg hI (fun k hk _ => by
      exact mul_nonneg (by positivity) (commonBlockEnergy_nonneg S β k))
  calc
    _ ≤ ∑ k ∈ I, K*A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ)*
        ((2:ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S β k) :=
      hsum.trans (Finset.sum_le_sum hb)
    _ = (K*A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ))*
        (∑ k ∈ I, (2:ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S β k) := by
      rw [Finset.mul_sum]
    _ ≤ (K*A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ))*(E*Z^(1/80000:ℝ)*∑ b ∈ S, ‖β b‖^2) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by
      have he : Z^(2/3-1/40000:ℝ)*Z^(1/80000:ℝ) = Z^(2/3-1/80000:ℝ) := by
        rw [← Real.rpow_add hZ]
        congr 1
        norm_num
      calc
        _ = (K*E)*A^(2/3:ℝ)*(Z^(2/3-1/40000:ℝ)*Z^(1/80000:ℝ))*∑ b ∈ S, ‖β b‖^2 := by ring
        _ = _ := by rw [he]

end CubicFirstMoment

end

end OAI
