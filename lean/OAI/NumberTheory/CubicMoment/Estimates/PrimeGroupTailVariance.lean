import OAI.NumberTheory.CubicMoment.Estimates.PrimeGroupTailCommonSum
import OAI.NumberTheory.CubicMoment.Estimates.SmallBCommonCutoff
import OAI.NumberTheory.CubicMoment.Estimates.LargeCommonSaving
import OAI.NumberTheory.CubicMoment.Estimates.CommonVarianceSum

namespace OAI

/-! Full arbitrary-coefficient variance in the small-B range. Every
common factor is retained; the zero mode has no divisor-energy loss. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem primeGroupTail_full_variance_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z A T u : ℝ), 65536 ≤ Z → Z^(27/25:ℝ) ≤ A → Z^(1/50:ℝ) ≤ T →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      dyadicHeightMean (fun t => ‖smoothedDispersionVariance S β (u+t) V A‖) T ≤
      K*(A+A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ))*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨K₁,hK₁,hsmall⟩ := primeGroupTail_common_sum_height_power hMV hC hHuxley V hV hV'
  obtain ⟨K₂,hK₂,hlarge⟩ := large_common_nonzero_power
    (δ := 1/1000) (by norm_num) (by norm_num) V hV hV'
  let c₀ := ‖normProfileFourier V 0‖/9
  have hc₀ : 0 ≤ c₀ := by dsimp [c₀]; positivity
  refine ⟨K₁+2*K₂+2*c₀,by positivity,?_⟩
  intro S β Z A T u hZ hA hT hS
  have hZ₁ : 1 ≤ Z := by linarith
  have hZp : 0 < Z := by linarith
  have hN : 1 ≤ Z/2 := by linarith
  have hNp : 0 < Z/2 := by positivity
  have hNZ : Z/2 ≤ Z := by linarith
  have hA₀ : 0 < A := (Real.rpow_pos_of_pos hZp _).trans_le hA
  have hT₀ : 0 < T := (Real.rpow_pos_of_pos hZp _).trans_le hT
  have hAN : (Z/2)^(1-1/1000:ℝ) ≤ A := by
    exact (Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (1-1/1000:ℝ) ≤ 27/25)).trans
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
    (fun b => star (dispersionAmplitude β (u+t) b)) V A k
  have hG : Continuous G := continuous_finsetSum I
    (fun k _ => continuous_commonGramBlock_height S β k V A u)
  have hGmean : dyadicHeightMean (fun t => ‖G t‖) T ≤ K₁*B*E := by
    simpa only [G,B,E,mul_assoc] using
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
  have hpoint (t : ℝ) : ‖smoothedDispersionVariance S β (u+t) V A‖ ≤
      ‖G t‖+(K₂*B*E+c₀*A*E) := by
    let v := fun b => star (dispersionAmplitude β (u+t) b)
    let L := ∑ k ∈ J, (commonGramBlock S v V A k-commonGramZeroMode S v V A k)
    let Q := ∑ k ∈ J, commonGramZeroMode S v V A k
    have hl : ‖L‖ ≤ K₂*B*E := by
      have hb := hlarge S v A (Z/2) hA₀ hN hAN hSr
      rw [henergy t] at hb
      exact hb.trans (by
        simpa only [B,mul_assoc] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow
            (show 0 ≤ K₂*A^(2/3:ℝ) by positivity)) hE)
    have hq : ‖Q‖ ≤ c₀*A*E := by
      have hb := commonGramZeroMode_sum_bound S J hS₀
        (fun k hk => commonRowFactors_spec hS₀ (Finset.mem_filter.mp hk).1) v V hA₀.le
      rwa [henergy t] at hb
    have he : smoothedDispersionVariance S β (u+t) V A = G t+L+Q := by
      rw [smoothedVariance_eq_commonGram S hS₀ β (u+t) V hV hV' hA₀]
      have hp := Finset.sum_filter_add_sum_filter_not (commonRowFactors S)
        (fun k => norm k < D) (fun k => commonGramBlock S v V A k)
      simp only [not_lt] at hp
      change (∑ k ∈ commonRowFactors S, commonGramBlock S v V A k) = _
      rw [← hp]
      dsimp only [G,L,Q,I,J]
      rw [add_assoc,← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [he]
    exact (norm_add_le _ _).trans ((add_le_add
      ((norm_add_le _ _).trans (add_le_add le_rfl hl)) hq).trans_eq (by ring))
  have hvc := (continuous_smoothedDispersionVariance S (fun b hb => (hS b hb).1)
    β V hV hV' hA₀).comp (show Continuous (fun t : ℝ => u+t) from continuous_const.add continuous_id)
  have hm := dyadicHeightMean_mono hvc.norm (hG.norm.add continuous_const) hT₀ (fun t _ => hpoint t)
  change dyadicHeightMean _ T ≤ dyadicHeightMean (fun t => ‖G t‖+(K₂*B*E+c₀*A*E)) T at hm
  rw [dyadicHeightMean_add hG.norm continuous_const,dyadicHeightMean_const _ hT₀.ne'] at hm
  apply hm.trans
  calc
    _ ≤ K₁*B*E+2*(K₂*B*E+c₀*A*E) := add_le_add hGmean le_rfl
    _ = (K₁+2*K₂)*B*E+(2*c₀)*A*E := by ring
    _ ≤ (K₁+2*K₂+2*c₀)*B*E+(K₁+2*K₂+2*c₀)*A*E := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith : K₁+2*K₂ ≤ K₁+2*K₂+2*c₀) hB) hE
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith : 2*c₀ ≤ K₁+2*K₂+2*c₀) hA₀.le) hE
    _ = _ := by dsimp [B,E]; ring

end CubicFirstMoment

end

end OAI
