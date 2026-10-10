import OAI.NumberTheory.CubicMoment.Estimates.ProfileCommonSmall
import OAI.NumberTheory.CubicMoment.Estimates.ProfileCommonLarge
import OAI.NumberTheory.CubicMoment.Estimates.SmallBVarianceRemainder

namespace OAI
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment.ProfileControl

theorem smallB_nonzero_variance_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : PoissonProfileBudget) (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z A T u : ℝ), 65536 ≤ Z → Z^(3/2:ℝ) ≤ A → Z^(1/50:ℝ) ≤ T →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      dyadicHeightMean (fun t => ‖∑ k ∈ commonRowFactors S,
        (commonGramBlock S (fun b => star (dispersionAmplitude β (u+t) b)) P.V A k-
         commonGramZeroMode S (fun b => star (dispersionAmplitude β (u+t) b)) P.V A k)‖) T ≤
      (K*P.cost)*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨L₁,hL₁,hsmall₀⟩ := smallB_common_sum_height_power hMV hC hHuxley
  obtain ⟨L₂,hL₂,hlarge₀⟩ := large_common_nonzero_power
    (δ := 1/1000) (by norm_num) (by norm_num)
  refine ⟨L₁+2*L₂,by positivity,?_⟩
  intro P S β Z A T u hZ hA hT hS
  let K₁ := L₁*P.cost
  let K₂ := L₂*P.cost
  have hK₁ : 0 < K₁ := mul_pos hL₁ P.cost_pos
  have hK₂ : 0 < K₂ := mul_pos hL₂ P.cost_pos
  have hsmall := hsmall₀ P
  have hlarge := hlarge₀ P
  have hZ₁ : 1 ≤ Z := by linarith
  have hZp : 0 < Z := by linarith
  have hN : 1 ≤ Z/2 := by linarith
  have hNp : 0 < Z/2 := by positivity
  have hNZ : Z/2 ≤ Z := by linarith
  have hA₀ : 0 < A := (Real.rpow_pos_of_pos hZp _).trans_le hA
  have hT₀ : 0 < T := (Real.rpow_pos_of_pos hZp _).trans_le hT
  have hAN : (Z/2)^(1-1/1000:ℝ) ≤ A := by
    exact (Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (1-1/1000:ℝ) ≤ 3/2)).trans
      ((Real.rpow_le_rpow hNp.le hNZ (by norm_num)).trans hA)
  have hS₀ : ∀ b ∈ S, primary b ∧ Squarefree b := fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩
  let D := (Z/2)^(1/1000:ℝ)
  let I := (commonRowFactors S).filter (fun k => norm k < D)
  let J := (commonRowFactors S).filter (fun k => D ≤ norm k)
  let E := ∑ b ∈ S, ‖β b‖^2
  let B := A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ)
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hfloor (k : Eisenstein) (hk : k ∈ I) :
      4 ≤ (⌊Z/norm k⌋₊:ℝ) ∧ 16 ≤ (⌊Z/norm k⌋₊:ℝ)^(3/4:ℝ) := by
    have hki := (Finset.mem_filter.mp hk)
    have hkp := (commonRowFactors_spec hS₀ hki.1).1
    apply smallB_common_floor_large hZ (norm_pos_of_ne_zero (primary_ne_zero hkp))
    exact hki.2.le.trans (Real.rpow_le_rpow hNp.le hNZ (by norm_num))
  let G (t : ℝ) := ∑ k ∈ I, commonGramBlock S
    (fun b => star (dispersionAmplitude β (u+t) b)) P.V A k
  have hG : Continuous G := continuous_finsetSum I
    (fun k _ => continuous_commonGramBlock_height S β k P.V A u)
  have hGmean : dyadicHeightMean (fun t => ‖G t‖) T ≤ K₁*B*E := by
    simpa only [G,B,E,K₁,mul_assoc] using
      hsmall S I β Z A T u hZp hA hT (Finset.filter_subset _ _) hfloor hS
  have henergy (t : ℝ) : (∑ b ∈ S, ‖star (dispersionAmplitude β (u+t) b)‖^2) = E := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [norm_star,dispersionAmplitude_norm_squarefree (hS b hb).1 (hS b hb).2.1]
  have hSr : ∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ 2*(Z/2) := by
    intro b hb
    exact ⟨(hS b hb).1,(hS b hb).2.1,(hS b hb).2.2.1,by nlinarith [(hS b hb).2.2.2]⟩
  have hpow : (Z/2)^(2/3-(1/1000)/8:ℝ) ≤ Z^(2/3-1/80000:ℝ) :=
    (Real.rpow_le_rpow hNp.le hNZ (by norm_num)).trans
      (Real.rpow_le_rpow_of_exponent_le hZ₁ (by norm_num))
  have hzero (t : ℝ) (k : Eisenstein) (hk : k ∈ I) :
      commonGramZeroMode S (fun b => star (dispersionAmplitude β (u+t) b)) P.V A k = 0 := by
    have hki := Finset.mem_filter.mp hk
    have hkp := commonRowFactors_spec hS₀ hki.1
    have hD : D ≤ Real.sqrt Z := by
      apply (Real.rpow_le_rpow hNp.le hNZ (by norm_num : (0:ℝ) ≤ 1/1000)).trans
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hZ₁ (by norm_num)
    have hroot : Real.sqrt Z ≤ Z/2 := by
      nlinarith [Real.sq_sqrt hZp.le,Real.sqrt_nonneg Z]
    have hknot : k ∉ S := by
      intro hks
      have hh := (hS k hks).2.2.1
      have hl := hki.2.trans_le (hD.trans hroot)
      linarith
    rw [commonGramZeroMode_eq S hS₀ _ P.V A hkp.1 hkp.2,ite_eq_right hknot]
  let F := fun t => ∑ k ∈ commonRowFactors S,
    (commonGramBlock S (fun b => star (dispersionAmplitude β (u+t) b)) P.V A k-
      commonGramZeroMode S (fun b => star (dispersionAmplitude β (u+t) b)) P.V A k)
  have hpoint (t : ℝ) : ‖F t‖ ≤ ‖G t‖+K₂*B*E := by
    let v := fun b => star (dispersionAmplitude β (u+t) b)
    let L := ∑ k ∈ J, (commonGramBlock S v P.V A k-commonGramZeroMode S v P.V A k)
    have hl : ‖L‖ ≤ K₂*B*E := by
      have hb := hlarge S v A (Z/2) hA₀ hN hAN hSr
      rw [henergy t] at hb
      exact hb.trans (by
        simpa only [B,K₂,mul_assoc] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow
            (show 0 ≤ K₂*A^(2/3:ℝ) by positivity)) hE)
    have he : F t = G t+L := by
      have hp := Finset.sum_filter_add_sum_filter_not (commonRowFactors S)
        (fun k => norm k < D) (fun k => commonGramBlock S v P.V A k-commonGramZeroMode S v P.V A k)
      simp only [not_lt] at hp
      rw [show F t = ∑ k ∈ commonRowFactors S,
          (commonGramBlock S v P.V A k-commonGramZeroMode S v P.V A k) from rfl,←hp]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [show commonGramZeroMode S v P.V A k = 0 from hzero t k hk,sub_zero]
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add le_rfl hl)
  have hfc : Continuous F := by
    apply continuous_finsetSum
    intro k hk
    apply (continuous_commonGramBlock_height S β k P.V A u).sub
    have hkp := commonRowFactors_spec hS₀ hk
    simp_rw [commonGramZeroMode_eq S hS₀ _ P.V A hkp.1 hkp.2]
    by_cases hks : k ∈ S
    · simp only [ite_eq_left hks]
      have hc : Continuous (fun t : ℝ => star (dispersionAmplitude β (u+t) k)) := by
        unfold dispersionAmplitude
        exact continuous_star.comp ((continuous_const.mul
          ((continuous_normTwist k).comp (continuous_const.add continuous_id))).mul continuous_const)
      exact (((hc.mul (continuous_star.comp hc)).mul continuous_const).mul continuous_const).mul
        continuous_const
    · simp only [ite_eq_right hks]
      exact continuous_const
  have hm := dyadicHeightMean_mono hfc.norm (hG.norm.add continuous_const) hT₀
    (fun t _ => hpoint t)
  change dyadicHeightMean _ T ≤ dyadicHeightMean (fun t => ‖G t‖+K₂*B*E) T at hm
  rw [dyadicHeightMean_add hG.norm continuous_const,dyadicHeightMean_const _ hT₀.ne'] at hm
  apply hm.trans
  calc
    _ ≤ K₁*B*E+2*(K₂*B*E) := add_le_add hGmean le_rfl
    _ = _ := by dsimp [B,E,K₁,K₂]; ring


theorem smallB_variance_remainder_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : PoissonProfileBudget) (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z A T u : ℝ), 65536 ≤ Z → Z^(3/2:ℝ) ≤ A → Z^(1/50:ℝ) ≤ T →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      dyadicHeightMean (fun t =>
        ‖smoothedDispersionVariance S β (u+t) P.V A-varianceZeroMode S β P.V A‖) T ≤
        (K*P.cost)*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨K,hK,hbound⟩ := smallB_nonzero_variance_height_power hMV hC hHuxley
  refine ⟨K,hK,?_⟩
  intro P S β Z A T u hZ hA hT hS
  have hA0 : 0 < A := (Real.rpow_pos_of_pos (by linarith : 0 < Z) _).trans_le hA
  simp_rw [variance_sub_zero_eq S (fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩)
    β _ P.V P.compact P.smooth hA0]
  exact hbound P S β Z A T u hZ hA hT hS


end CubicFirstMoment.ProfileControl

end

end OAI
