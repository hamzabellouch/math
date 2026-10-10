import OAI.NumberTheory.CubicMoment.Estimates.LowCommonSum
import OAI.NumberTheory.CubicMoment.Estimates.ProfileCommonLarge
import OAI.NumberTheory.CubicMoment.Estimates.LowLargeScale
import OAI.NumberTheory.CubicMoment.Estimates.SmallBVarianceRemainder

namespace OAI
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment.ProfileControl

theorem low_nonzero_variance_height_log_saving
    (hpnt : PrimaryPrimePNT) (j : ℕ)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ (P : PoissonProfileBudget) (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z A T M u : ℝ), (65536:ℝ)^2 ≤ Z → Z^(3/2:ℝ) ≤ A →
      (1+Real.log Z)^Ct ≤ T → 0 ≤ M →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      dyadicHeightMean (fun t => ‖∑ k ∈ commonRowFactors S,
        (commonGramBlock S (fun b => star (dispersionAmplitude β (u+t) b)) P.V A k-
         commonGramZeroMode S (fun b => star (dispersionAmplitude β (u+t) b)) P.V A k)‖) T ≤
      (K*P.cost)*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^j := by
  obtain ⟨L₁,Ct,hL₁,hsmall₀⟩ := low_common_sum_height_log_saving hpnt j hMV hC hHuxley
  obtain ⟨L₂,hL₂,hlarge₀⟩ := large_common_nonzero_power
    (δ := 1/1000) (by norm_num) (by norm_num)
  obtain ⟨D₀,hD₀,hlogscale⟩ := low_large_common_log_scale j
  refine ⟨L₁+36*L₂*D₀,Ct,by positivity,?_⟩
  intro P S β Z A T M u hZ hA hT hM hS hβ
  let K₁ := L₁*P.cost
  let K₂ := L₂*P.cost
  have hK₁ : 0 < K₁ := mul_pos hL₁ P.cost_pos
  have hK₂ : 0 < K₂ := mul_pos hL₂ P.cost_pos
  have hsmall := hsmall₀ P
  have hlarge := hlarge₀ P
  have hZ₁ : 1 ≤ Z := by linarith
  have hL : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ₁]
  have hZp : 0 < Z := by linarith
  have hN : 1 ≤ Z/2 := by linarith
  have hNp : 0 < Z/2 := by positivity
  have hNZ : Z/2 ≤ Z := by linarith
  have hA₀ : 0 < A := (Real.rpow_pos_of_pos hZp _).trans_le hA
  have hT₀ : 0 < T := (pow_pos (by linarith [Real.log_nonneg hZ₁]) _).trans_le hT
  have hAN : (Z/2)^(1-1/1000:ℝ) ≤ A := by
    exact (Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (1-1/1000:ℝ) ≤ 3/2)).trans
      ((Real.rpow_le_rpow hNp.le hNZ (by norm_num)).trans hA)
  have hS₀ : ∀ b ∈ S, primary b ∧ Squarefree b := fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩
  let D := (Z/2)^(1/1000:ℝ)
  let I := (commonRowFactors S).filter (fun k => norm k < D)
  let J := (commonRowFactors S).filter (fun k => D ≤ norm k)
  let E := M^2
  let B := A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^j
  have hE : 0 ≤ E := sq_nonneg _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsmallnorm (k : Eisenstein) (hk : k ∈ I) : norm k ≤ Z^(1/2:ℝ) := by
    have hki := (Finset.mem_filter.mp hk).2
    apply hki.le.trans
    exact (Real.rpow_le_rpow hNp.le hNZ (by norm_num)).trans
      (Real.rpow_le_rpow_of_exponent_le hZ₁ (by norm_num))
  let G (t : ℝ) := ∑ k ∈ I, commonGramBlock S
    (fun b => star (dispersionAmplitude β (u+t) b)) P.V A k
  have hG : Continuous G := continuous_finsetSum I
    (fun k _ => continuous_commonGramBlock_height S β k P.V A u)
  have hGmean : dyadicHeightMean (fun t => ‖G t‖) T ≤ K₁*B*E := by
    apply (hsmall S I β Z A T M u hZ hA hT hM (Finset.filter_subset _ _) hsmallnorm hS hβ).trans_eq
    dsimp [B,E,K₁]
    ring
  have henergy (t : ℝ) : (∑ b ∈ S, ‖star (dispersionAmplitude β (u+t) b)‖^2) ≤ 18*Z*M^2 := by
    have hcard := primary_support_card_le S hZp.le
      (fun b hb => ⟨(hS b hb).1,(hS b hb).2.2.2⟩)
    calc
      _ ≤ ∑ _b ∈ S, M^2 := by
        apply Finset.sum_le_sum
        intro b hb
        rw [norm_star,dispersionAmplitude_norm_squarefree (hS b hb).1 (hS b hb).2.1]
        exact pow_le_pow_left₀ (_root_.norm_nonneg _) (hβ b hb) 2
      _ = (S.card:ℝ)*M^2 := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
  have hSr : ∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ 2*(Z/2) := by
    intro b hb
    exact ⟨(hS b hb).1,(hS b hb).2.1,(hS b hb).2.2.1,by nlinarith [(hS b hb).2.2.2]⟩
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
  have hpoint (t : ℝ) : ‖F t‖ ≤ ‖G t‖+(18*K₂*D₀)*B*E := by
    let v := fun b => star (dispersionAmplitude β (u+t) b)
    let L := ∑ k ∈ J, (commonGramBlock S v P.V A k-commonGramZeroMode S v P.V A k)
    have hl : ‖L‖ ≤ (18*K₂*D₀)*B*E := by
      have hb := hlarge S v A (Z/2) hA₀ hN hAN hSr
      apply hb.trans
      calc
        _ ≤ K₂*A^(2/3:ℝ)*(Z/2)^(2/3-(1/1000)/8:ℝ)*(18*Z*M^2) :=
          mul_le_mul_of_nonneg_left (henergy t) (by positivity)
        _ = (18*K₂*A^(2/3:ℝ)*M^2)*((Z/2)^(2/3-1/8000:ℝ)*Z) := by
          norm_num
          ring
        _ ≤ (18*K₂*A^(2/3:ℝ)*M^2)*(D₀*Z^(5/3:ℝ)/(1+Real.log Z)^j) :=
          mul_le_mul_of_nonneg_left (hlogscale Z (by nlinarith)) (by positivity)
        _ = _ := by dsimp [B,E]; ring
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
  change dyadicHeightMean _ T ≤ dyadicHeightMean (fun t => ‖G t‖+(18*K₂*D₀)*B*E) T at hm
  rw [dyadicHeightMean_add hG.norm continuous_const,dyadicHeightMean_const _ hT₀.ne'] at hm
  apply hm.trans
  calc
    _ ≤ K₁*B*E+2*((18*K₂*D₀)*B*E) := add_le_add hGmean le_rfl
    _ = _ := by dsimp [B,E,K₁,K₂]; ring


theorem low_variance_remainder_height_log_saving
    (hpnt : PrimaryPrimePNT) (j : ℕ)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ (P : PoissonProfileBudget) (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z A T M u : ℝ), (65536:ℝ)^2 ≤ Z → Z^(3/2:ℝ) ≤ A →
      (1+Real.log Z)^Ct ≤ T → 0 ≤ M →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      dyadicHeightMean (fun t =>
        ‖smoothedDispersionVariance S β (u+t) P.V A-varianceZeroMode S β P.V A‖) T ≤
        (K*P.cost)*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^j := by
  obtain ⟨K,Ct,hK,hbound⟩ := low_nonzero_variance_height_log_saving hpnt j hMV hC hHuxley
  refine ⟨K,Ct,hK,?_⟩
  intro P S β Z A T M u hZ hA hT hM hS hβ
  have hA0 : 0 < A := (Real.rpow_pos_of_pos (by linarith : 0 < Z) _).trans_le hA
  simp_rw [variance_sub_zero_eq S (fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩)
    β _ P.V P.compact P.smooth hA0]
  exact hbound P S β Z A T M u hZ hA hT hM hS hβ


end CubicFirstMoment.ProfileControl

end

end OAI
