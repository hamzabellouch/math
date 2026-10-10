import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightLeaf
import OAI.NumberTheory.Ostmann.Characters.HistoryReconstruction

namespace OAI

noncomputable section
open scoped FourierTransform ComplexConjugate
namespace Ostmann.Characters.HistoryReconstruction
attribute [local instance] Classical.propDecidable
open Arithmetic

def characterLeafWeight (X Δ W:ℝ) (s:ℤ) (x:List ℤ) : ℂ :=
  if 0<(x.prod:ℝ) ∧ Real.log X+Δ-W≤Real.log (x.prod:ℝ) then
    (Real.sqrt (X/(x.prod:ℝ)):ℂ)*𝓕 SchwartzCutoff.psi (-(s:ℝ)*X/(x.prod:ℝ))
  else 0

def characterWeight (plan:Plan) (mask:ℕ→ℤ→List ℤ→Prop) (X Δ W:ℝ) :
    (k:ℕ) → ℤ → List ℤ → Tree k → ℂ
  | 0,s,x,_ => if mask 0 s x then characterLeafWeight X Δ W s x else 0
  | k+1,s,x,t =>
      if mask (k+1) s x then
        let P := pivot (plan.copiedSize k) x s t.1.1 t.1.2
        characterWeight plan mask X Δ W k t.1.1 (childState plan k false x P) t.2.1 *
          conj (characterWeight plan mask X Δ W k t.1.2 (childState plan k true x P) t.2.2)
      else 0

theorem characterLeafWeight_norm_le (X Δ W:ℝ) (hX:0<X) (s:ℤ) (x:List ℤ) :
    ‖characterLeafWeight X Δ W s x‖≤leafFourierBound*Real.exp ((-Δ+W)/2) := by
  unfold characterLeafWeight
  split_ifs with h
  · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ ≤ Real.sqrt (X/(x.prod:ℝ))*leafFourierBound :=
        mul_le_mul_of_nonneg_left (norm_fourier_psi_le _) (Real.sqrt_nonneg _)
      _ ≤ _ := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left
          (sqrt_ratio_le_of_log_lower X (x.prod:ℝ) Δ W hX h.1 h.2) leafFourierBound_pos.le
  · rw [norm_zero]
    exact mul_nonneg leafFourierBound_pos.le (Real.exp_pos _).le

theorem characterWeight_norm_le (plan:Plan) (mask:ℕ→ℤ→List ℤ→Prop)
    (X Δ W:ℝ) (hX:0<X) (k:ℕ) (s:ℤ) (x:List ℤ) (t:Tree k) :
    ‖characterWeight plan mask X Δ W k s x t‖≤
      (leafFourierBound*Real.exp ((-Δ+W)/2))^(2^k) := by
  have hC : 0≤leafFourierBound*Real.exp ((-Δ+W)/2) :=
    mul_nonneg leafFourierBound_pos.le (Real.exp_pos _).le
  induction k generalizing s x with
  | zero =>
    change ‖if mask 0 s x then characterLeafWeight X Δ W s x else 0‖≤_
    split_ifs
    · simpa only [pow_zero,pow_one] using characterLeafWeight_norm_le X Δ W hX s x
    · rw [norm_zero]; positivity
  | succ k ih =>
    rw [characterWeight]
    split_ifs
    · rw [norm_mul,Complex.norm_conj]
      calc
        _ ≤ (leafFourierBound*Real.exp ((-Δ+W)/2))^(2^k)*
            (leafFourierBound*Real.exp ((-Δ+W)/2))^(2^k) :=
          mul_le_mul (ih _ _ t.2.1) (ih _ _ t.2.2) (norm_nonneg _) (pow_nonneg hC _)
        _ = _ := by rw [← pow_add]; congr 1; omega
    · rw [norm_zero]; exact pow_nonneg hC _

theorem characterWeight_norm_sq_le (plan:Plan) (mask:ℕ→ℤ→List ℤ→Prop)
    (X Δ W:ℝ) (hX:0<X) (k:ℕ) (s:ℤ) (x:List ℤ) (t:Tree k) :
    ‖characterWeight plan mask X Δ W k s x t‖^2≤
      (leafFourierBound*Real.exp ((-Δ+W)/2))^((2^k)*2) := by
  have hh := pow_le_pow_left₀ (norm_nonneg _) (characterWeight_norm_le plan mask X Δ W hX k s x t) 2
  simpa only [← pow_mul] using hh

end Ostmann.Characters.HistoryReconstruction

end

end OAI
