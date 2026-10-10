import OAI.NumberTheory.TotientAsymptotic.FailedRowCountBound

namespace OAI

/-! Explicit residual cutoffs satisfying every first-failed-row mass budget. -/
noncomputable section
namespace TotientAsymptotic

def failedRowCutoff (F ω : ℝ) (k : ℕ) : ℝ :=
  Real.exp (Real.exp (rowMassCutoffHeight F (coordinateDecay (ω/4) k)))

lemma failed_row_cutoff_loglog (F ω : ℝ) (k : ℕ) :
    B (failedRowCutoff F ω k)=rowMassCutoffHeight F (coordinateDecay (ω/4) k) := by
  simp only [B,failedRowCutoff,Real.log_exp]

lemma failed_row_cutoff_budget {F ω : ℝ} (hF : 0 ≤ F) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (k : ℕ) : FailedRowMassBudget F ω (failedRowCutoff F ω k) k := by
  let δ := coordinateDecay (ω/4) k
  let b := rowMassCutoffHeight F δ
  have hδ : 0 < δ := coordinate_decay_pos (by linarith) k
  have hδ1 : δ ≤ 1 :=
    (coordinate_decay_bounds (k:=k) (by linarith : 0 ≤ ω/4) (by linarith : ω/4 ≤ 1)).2.1.trans
      (by norm_num)
  have hp : 1 ≤ ((k:ℝ)+2)^6 := one_le_pow₀ (by have := Nat.cast_nonneg (α:=ℝ) k; linarith)
  have hδω : 64000000*δ ≤ ω^2 := by
    have hd : 12000000 ≤ 12000000*((k:ℝ)+2)^6 := by nlinarith only [hp]
    have hh := div_le_div_of_nonneg_left (sq_nonneg (ω/4)) (by norm_num : (0:ℝ)<12000000) hd
    change δ ≤ (ω/4)^2/12000000 at hh
    have he : (ω/4)^2/12000000=ω^2/192000000 := by ring
    rw [he] at hh
    nlinarith only [hh,sq_nonneg ω]
  obtain ⟨hb,hhead,hthreshold,hlarge,hinv⟩ := row_mass_cutoff_height_bounds hF hδ hδ1 hω hω1 hδω
  change 10000 ≤ b at hb
  have hBU : B (failedRowCutoff F ω k)=b := failed_row_cutoff_loglog F ω k
  have hexp := Real.add_one_le_exp b
  have hexpexp := Real.add_one_le_exp (Real.exp b)
  have hU : 512 ≤ failedRowCutoff F ω k := by
    change 512 ≤ Real.exp (Real.exp b)
    linarith only [hb,hexp,hexpexp]
  have hUexp : 2*Real.exp (Real.exp 1) ≤ failedRowCutoff F ω k := by
    have hlog : Real.log (2*Real.exp (Real.exp 1)) ≤ Real.exp b := by
      rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (Real.exp_ne_zero _),Real.log_exp]
      have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      linarith only [hl2,Real.exp_one_lt_three,hb,hexp]
    change 2*Real.exp (Real.exp 1) ≤ Real.exp (Real.exp b)
    exact (Real.log_le_iff_le_exp (by positivity)).mp hlog
  unfold FailedRowMassBudget
  rw [hBU]
  exact ⟨hω,hω1,hU,hUexp,hb,hhead,hthreshold,hlarge,hinv⟩

end TotientAsymptotic

end

end OAI
