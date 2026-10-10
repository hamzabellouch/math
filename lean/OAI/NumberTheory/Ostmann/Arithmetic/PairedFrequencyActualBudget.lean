import OAI.NumberTheory.Ostmann.Arithmetic.PairedFrequencyActualBudgetEnvelope

namespace OAI

noncomputable section
open Filter
open scoped BigOperators
namespace Ostmann.Arithmetic.PairedFrequencyActualBudget
open Conclusion Characters

def actualBudget (C D ε δ Bs BD Bz : ℝ) (k : ℕ) (L : ℝ) (l : ℕ) : ℝ :=
  FrequencyTreeSum.budget (pairedRanges Bs BD Bz k L l)
    (PairedFrequencyTreeSum.nodeBudget C D ε δ (addressBound Bs BD Bz k L l)) l []

theorem actualBudget_le_exp {C D ε δ Bs BD Bz : ℝ}
    (hC : 0 ≤ C) (hD : 0 < D) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz)
    {k : ℕ} (hk : 0 < k) (L : ℝ) (hm : 1 ≤ bulkSize k L)
    {l : ℕ} (hl : l ≤ k) :
    actualBudget C D ε δ Bs BD Bz k L l ≤
      Real.exp ((2:ℝ)^l*(2*initialGap Bs k L+2*Real.sqrt (bulkSize k L)+2*Real.log 2)+
        ((2:ℝ)^l-1)*nodeExponent C D ε δ (scaleLinearConstant Bs BD Bz k) (bulkSize k L)) := by
  apply budget_exp_bound (N:=l)
  · intro p
    have hlog : 0 ≤ Real.log (addressBound Bs BD Bz k L l p) :=
      Real.log_nonneg (by exact_mod_cast addressBound_pos hBs hBD hBz hk L l p)
    unfold PairedFrequencyTreeSum.nodeBudget
    positivity
  · intro p
    exact nodeBudget_le_exp hC hD hε hδ (scaleLinearConstant_pos Bs BD Bz k).le
      (by exact_mod_cast hm) _ (addressBound_pos hBs hBD hBz hk L l)
      (addressBound_le_exp Bs BD Bz k L l hl hm) p
  · exact paired_leaf_card_le Bs BD Bz k L l
  · simp

theorem scalar_envelope_le {h H gap C d m : ℝ}
    (hh : h ≤ H) (hC : 0 ≤ C) (hd : 0 ≤ d) (hm : 0 ≤ m) :
    h*(2*gap+2*Real.sqrt m+2*Real.log 2)+(h-1)*(C+d*m+6*Real.sqrt m) ≤
      2*h*gap+(H*d)*m+8*H*Real.sqrt m+H*(C+2*Real.log 2) := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hn := mul_le_mul_of_nonneg_right (show h-1 ≤ H by linarith)
    (show 0 ≤ C+d*m+6*Real.sqrt m by positivity)
  have hr := mul_le_mul_of_nonneg_right hh
    (show 0 ≤ 2*Real.sqrt m+2*Real.log 2 by positivity)
  nlinarith

theorem exists_eventually_actualBudget_le {Bs BD Bz : ℝ}
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz)
    {k : ℕ} (hk : 0 < k) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ C D : ℝ, 0 ≤ C → 0 < D →
        ∀ᶠ L : ℝ in atTop, ∀ l ≤ k,
          actualBudget C D ε δ Bs BD Bz k L l ≤
            Real.exp (2*(2:ℝ)^l*initialGap Bs k L+ρ*(bulkSize k L:ℝ)) := by
  let A := scaleLinearConstant Bs BD Bz k
  let H : ℝ := 2^k
  let ε := ρ/(8*H*A)
  have hA : 0 < A := scaleLinearConstant_pos Bs BD Bz k
  have hH : 0 < H := by dsimp [H]; positivity
  have he : 0 < ε := div_pos hρ (by positivity)
  refine ⟨ε,ε,he,he,?_⟩
  intro C D hC hD
  have hcoef : H*((2*ε+2*ε)*A)=ρ/2 := by
    dsimp [ε]
    field_simp
    ring
  have habs := (bulkSize_tendsto_atTop hk).eventually
    (HistoryFrequencyBudget.eventually_const_sqrt_le (8*H)
      (H*(nodeConstant C D A+2*Real.log 2)) (ρ/2) (by positivity))
  have hm := (bulkSize_tendsto_atTop hk).eventually (eventually_ge_atTop (1:ℝ))
  filter_upwards [habs,hm] with L habs hm
  intro l hl
  have hmN : 1 ≤ bulkSize k L := by exact_mod_cast hm
  have hh : (2:ℝ)^l ≤ H := pow_le_pow_right₀ (by norm_num) hl
  have hb := actualBudget_le_exp hC hD he.le he.le hBs hBD hBz hk L hmN hl
  apply hb.trans
  apply Real.exp_le_exp.mpr
  change (2:ℝ)^l*(2*initialGap Bs k L+2*Real.sqrt (bulkSize k L)+2*Real.log 2)+
    ((2:ℝ)^l-1)*(nodeConstant C D A+(2*ε+2*ε)*A*(bulkSize k L:ℝ)+
      6*Real.sqrt (bulkSize k L)) ≤ _
  have hs := scalar_envelope_le (gap:=initialGap Bs k L)
    (m:=(bulkSize k L:ℝ)) hh (nodeConstant_nonneg (C:=C) (D:=D) hA.le)
      (show 0 ≤ (2*ε+2*ε)*A by positivity) (Nat.cast_nonneg _)
  rw [hcoef] at hs
  nlinarith

end Ostmann.Arithmetic.PairedFrequencyActualBudget

end

end OAI
