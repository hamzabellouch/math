import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedPairDerivativeBoundsBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedPairDerivativeBounds
open Construction Characters.RationalHistory HistoryOccurrenceVariables HistoryPairSmoothXi
open HistorySymbolicEncoding HistoryProductWindows

def coreExponent (k : ℕ) (E CK : ℝ) : ℝ :=
  |Real.log (sourceDerivativePrefactor k E)|+1+CK*(k:ℝ)

lemma coreExponent_pos (k : ℕ) (E : ℝ) {CK : ℝ} (hCK : 0 ≤ CK) :
    0 < coreExponent k E CK := by
  unfold coreExponent
  positivity

def pairExponent (k : ℕ) (E CK N : ℝ) : ℝ :=
  |Real.log N|+1+coreExponent k E CK

lemma pairExponent_pos (k : ℕ) (E N : ℝ) {CK : ℝ} (hCK : 0 ≤ CK) :
    0 < pairExponent k E CK N := by
  have := coreExponent_pos k E hCK
  unfold pairExponent
  positivity

theorem pairDerivativeBound_le_exp {b k l : ℕ} {V : ℕ → ℕ}
    {tb Δ E CK N m : ℝ} (center : ℕ → ℝ) (h g : History l)
    (hl : l ≤ k) (hΔ : 0 ≤ Δ) (hCK : 0 ≤ CK) (hN : 0 < N)
    (hm : 1 ≤ m) (hb : (b:ℝ) ≤ m)
    (hK : sourceCancellationBound V b k tb center l ≤ Real.exp (CK*m))
    (hcard : (Fintype.card (Key h):ℝ)+Fintype.card (Key g) ≤ N*(m+1)) :
    pairDerivativeBound h g V b k tb Δ E center ≤
      Real.exp (pairExponent k E CK N*(m+1)) := by
  have hd := source_derivative_core_le (E:=E) center hl hΔ hCK hm hb hK
  have hd' : Real.exp (-((2^l:ℕ):ℝ)*Δ+sourceXiConstant l k E)*historyDerivativeCount l*
      actualSourceDerivativeRate (sourceHistoryBudget V b k l tb center) ≤
      Real.exp (coreExponent k E CK*(m+1)) := by
    exact hd.trans (Real.exp_le_exp.mpr (by
      change coreExponent k E CK*m ≤ coreExponent k E CK*(m+1)
      nlinarith [coreExponent_pos k E hCK]))
  have hp := mul_le_mul hcard hd'
    (mul_nonneg (mul_nonneg (Real.exp_nonneg _) (historyDerivativeCount_nonneg l))
      (actualSourceDerivativeRate_nonneg (sourceHistoryBudget_nonneg _ _ _ _ _ _)))
    (by positivity : 0 ≤ N*(m+1))
  have he := linear_prefactor_mul_exp_le N (coreExponent k E CK) (m+1) hN
    (coreExponent_pos k E hCK).le (by linarith)
  unfold pairDerivativeBound
  dsimp only [pairExponent]
  calc
    _ = ((Fintype.card (Key h):ℝ)+Fintype.card (Key g))*
        (Real.exp (-((2^l:ℕ):ℝ)*Δ+sourceXiConstant l k E)*historyDerivativeCount l*
          actualSourceDerivativeRate (sourceHistoryBudget V b k l tb center)) := by ring
    _ ≤ N*(m+1)*Real.exp (coreExponent k E CK*(m+1)) := hp
    _ ≤ _ := he

theorem correctedPairDerivativeBound_le_exp {b k l Hlen Ulen cellCount : ℕ}
    {V : ℕ → ℕ} {tb Δ E CK N W WH Wu m : ℝ}
    (center : ℕ → ℝ) (h g : History l)
    (hl : l ≤ k) (hΔ : 0 ≤ Δ) (hCK : 0 ≤ CK) (hN : 0 < N) (_hW : 0 ≤ W)
    (hm : 1 ≤ m) (hb : (b:ℝ) ≤ m)
    (hK : sourceCancellationBound V b k tb center l ≤ Real.exp (CK*m))
    (hcard : (Fintype.card (Key h):ℝ)+Fintype.card (Key g) ≤ N*(m+1))
    (hwidth : WH+Wu ≤ W*(m+1))
    (hcount : (Hlen:ℝ)+Ulen+rootCounterpartDerivativeConstant*cellCount ≤ N*(m+1)) :
    correctedPairDerivativeBound WH Wu Hlen Ulen cellCount h g V b k tb Δ E center ≤
      Real.exp ((W+pairExponent k E CK N+
        (|Real.log N|+1+amplitudeConstant k E)+1)*(m+1)) := by
  have ha := source_amplitude_le hl hΔ (E:=E)
  have ha' := ha.trans (Real.exp_le_exp.mpr
    (le_mul_of_one_le_right (amplitudeConstant_nonneg k E) (by linarith : 1 ≤ m+1)))
  have hp := pairDerivativeBound_le_exp (E:=E) center h g hl hΔ hCK hN hm hb hK hcard
  have htail : Real.exp (-((2^l:ℕ):ℝ)*Δ+sourceXiConstant l k E)*
      ((Hlen:ℝ)+Ulen+rootCounterpartDerivativeConstant*cellCount) ≤
      Real.exp ((|Real.log N|+1+amplitudeConstant k E)*(m+1)) := by
    calc
      _ ≤ Real.exp (amplitudeConstant k E*(m+1))*(N*(m+1)) :=
        mul_le_mul ha' hcount
          (by positivity [rootCounterpartDerivativeConstant_pos]) (Real.exp_nonneg _)
      _ = N*(m+1)*Real.exp (amplitudeConstant k E*(m+1)) := by ring
      _ ≤ _ := linear_prefactor_mul_exp_le N (amplitudeConstant k E) (m+1)
        hN (amplitudeConstant_nonneg k E) (by linarith)
  have hs := add_exp_bounds (by linarith : 1 ≤ m+1) (pairExponent_pos k E N hCK).le
    (by positivity [amplitudeConstant_nonneg k E] : 0 ≤ |Real.log N|+1+amplitudeConstant k E) hp htail
  unfold correctedPairDerivativeBound
  calc
    _ ≤ Real.exp (W*(m+1))*Real.exp ((pairExponent k E CK N+
        (|Real.log N|+1+amplitudeConstant k E)+1)*(m+1)) :=
      mul_le_mul (Real.exp_le_exp.mpr hwidth) hs
        (by positivity [pairDerivativeBound_nonneg h g V b k tb Δ E center,
          rootCounterpartDerivativeConstant_pos]) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Ostmann.Arithmetic.HistorySelectedPairDerivativeBounds

end

end OAI
