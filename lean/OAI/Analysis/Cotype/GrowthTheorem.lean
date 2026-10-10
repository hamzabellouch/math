import OAI.Analysis.Cotype.RankWalsh

namespace OAI

noncomputable section

universe u v
namespace Cotype

theorem exists_growth_constant (m : ℕ) (Dg Df : ℝ)
    (hDg1 : 1 ≤ Dg) (hDf1 : 1 ≤ Df)
    (hcut : 4 ≤ degreeCutoff m) (hcutm : degreeCutoff m < m)
    (hsize : 80 * (degreeCutoff m : ℝ) * (degreeCutoff m + 1 : ℝ)^2 ≤
      min ((m : ℝ)*(1/(2*24*Dg*Real.sqrt m))) ((m : ℝ)*(1/(2*24*Df*Real.sqrt m)))) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1/2 ∧
      ∀ (X : Type u) (Y : Type v) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
        [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : X →L[ℝ] Y),
        FixedCotypeBound (X →L[ℝ] ℝ) m Dg → FixedCotypeBound Y m Df → T ≠ 0 →
        ∀ n : ℕ, 4*m < n → walshNorm (n-2*m) T ≤ 2*walshNorm n T →
          c₁ * walshNorm n T ≤ walshNorm (2*(n-2*m)) T := by
  have hm : 0 < m := by omega
  have hmg : 0 < 1/(2*24*Dg*Real.sqrt m) := by
    have : 0 < Dg := by linarith
    positivity
  have hmf : 0 < 1/(2*24*Df*Real.sqrt m) := by
    have : 0 < Df := by linarith
    positivity
  obtain ⟨c,hc,hall⟩ := coefficientTarget_proved m _ _ hcut hcutm hmg hmf hsize
  refine ⟨min (1/2) (c/2), lt_min (by norm_num) (by positivity), min_le_left _ _, ?_⟩
  intro X Y _ _ _ _ _ T hDg hDf hT n hn hslow
  obtain ⟨k,rfl⟩ : ∃ k, n = k+m+m := ⟨n-2*m, by omega⟩
  have he : k+m+m-2*m = k := by omega
  rw [he] at hslow ⊢
  obtain ⟨d⟩ := exists_growthPairingData (k+m+m) hm hDg hDf hDg1 hDf1 hT
  have hnm : m+m ≤ k+m+m := by omega
  have hnp : m+1 ≤ k+m+m := by omega
  have hnd : 1+m ≤ k+m+m := by omega
  obtain ⟨P,hPr,hPc⟩ := hall (d.normalizedMatrix hnm) (d.normalizedPrimal hnp)
    (d.normalizedDual hnd) (d.normalized_scalar_admissible hm hnm hnp hnd hslow)
  obtain ⟨ε,δ,hfix⟩ := d.exists_fixed_lift_coefficient hnm P hc hPc
  have hrank := d.coefficient_rank_walsh_bound hnm P ε δ
  have hmono := walshNorm_antitone T (Nat.mul_le_mul_right k hPr)
  have hcg : c*d.gamma ≤ walshNorm (2*k) T := hfix.trans (hrank.trans hmono)
  have hc1 := min_le_right (1/2 : ℝ) (c/2)
  have hn0 := walshNorm_nonneg (k+m+m) T
  have hhalf := d.gamma_half
  nlinarith [mul_le_mul_of_nonneg_right hc1 hn0]

end Cotype

end

end OAI
