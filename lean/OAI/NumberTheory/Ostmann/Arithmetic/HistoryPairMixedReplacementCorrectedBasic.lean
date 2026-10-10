import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairActiveReindex
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightCorrected
import OAI.NumberTheory.Ostmann.Construction.DiagonalRegroupingRootCorrection

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairSmoothXi
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistoryPairPattern HistorySymbolicEncoding InitialCoordinatesTemplate HistoryActiveCoordinates
open HistoryRepeatedSmoothPullback
open scoped ContDiff
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

def correctedPairedRealXi (b s : ℕ) (X tb td G : ℝ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) {τ : Type}
    (T U : ℝ) (Hkeys Ukeys : List (PairKey h k))
    (S : Finset τ) (cellCenter : τ → ℝ) (cellKey : τ → PairKey h k) (x : PairKey h k → ℝ) : ℂ :=
  (rootCounterpart T U Hkeys Ukeys S cellCenter cellKey x : ℂ) *
    pairedRealXi b s X tb td G h k hs ks x

theorem correctedPairedRealXi_log_contDiff (b s : ℕ) (X tb td G : ℝ) (hX : 0 < X)
    (houtside : ∀q ∈ outside,0 < q) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) {τ : Type}
    (T U : ℝ) (Hkeys Ukeys : List (PairKey h k))
    (S : Finset τ) (cellCenter : τ → ℝ) (cellKey : τ → PairKey h k) :
    ContDiff ℝ ∞ (fun y : PairKey h k → ℝ =>
      correctedPairedRealXi b s X tb td G h k hs ks T U Hkeys Ukeys S cellCenter cellKey
        (fun i => Real.exp (y i))) := by
  exact (Complex.ofRealCLM.contDiff.comp
    (rootCounterpart_contDiff_exp T U Hkeys Ukeys S cellCenter cellKey)).mul
    (pairedRealXi_log_contDiff b s X tb td G hX houtside h k hs ks)

theorem correctedPairedRealXi_norm_le (b s k₀ : ℕ) (X tb td G Δ E : ℝ)
    (center : ℕ → ℝ) (hX : 0 < X) (houtside : ∀q ∈ outside,0 < q)
    (hout : outside.length = 2*s) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) {τ : Type}
    (T U WH Wu : ℝ) (Hkeys Ukeys : List (PairKey h k))
    (S : Finset τ) (cellCenter : τ → ℝ) (cellKey : τ → PairKey h k) (x : PairKey h k → ℝ)
    (hx : ∀i,0 < x i) (hH : T-WH ≤ Real.log ((Hkeys.map x).prod))
    (hu : Real.log ((Ukeys.map x).prod) ≤ U+Wu)
    (hx₁ : SourceDomain b k₀ G center h (fun i => x (leftMap h k i)))
    (hx₂ : SourceDomain b k₀ G center k (fun i => x (rightMap h k i)))
    (hcenter : Real.log X+Δ-E ≤ 2*G+2*tb+2*td+
      (∑a,∑i,topCenters b center a i)+
      (∑a,∑j : Fin k₀,∑i,compensationCenters b center a j i)) :
    ‖correctedPairedRealXi b s X tb td G h k hs ks T U Hkeys Ukeys S cellCenter cellKey x‖ ≤
      Real.exp (WH+Wu) * Real.exp (-((2^l:ℕ):ℝ)*Δ+sourceXiConstant l k₀ E) := by
  rw [correctedPairedRealXi,norm_mul]
  exact mul_le_mul (rootCounterpart_norm_le T U WH Wu Hkeys Ukeys S cellCenter cellKey x hx hH hu)
    (pairedRealXi_norm_le b s k₀ X tb td G Δ E center hX houtside hout h k hs ks x hx₁ hx₂ hcenter)
    (norm_nonneg _) (Real.exp_pos _).le

def correctedPairDerivativeBound (WH Wu : ℝ) (Hlen Ulen cellCount : ℕ)
    (h k : History l) (V : ℕ → ℕ) (b k₀ : ℕ) (tb Δ E : ℝ) (center : ℕ → ℝ) : ℝ :=
  Real.exp (WH+Wu) * (pairDerivativeBound h k V b k₀ tb Δ E center +
    Real.exp (-((2^l:ℕ):ℝ)*Δ+sourceXiConstant l k₀ E) *
      ((Hlen:ℝ)+Ulen+rootCounterpartDerivativeConstant*cellCount))

theorem correctedPairDerivativeBound_nonneg (WH Wu : ℝ) (Hlen Ulen cellCount : ℕ)
    (h k : History l) (V : ℕ → ℕ) (b k₀ : ℕ) (tb Δ E : ℝ) (center : ℕ → ℝ) :
    0 ≤ correctedPairDerivativeBound WH Wu Hlen Ulen cellCount h k V b k₀ tb Δ E center := by
  unfold correctedPairDerivativeBound
  positivity [pairDerivativeBound_nonneg h k V b k₀ tb Δ E center,rootCounterpartDerivativeConstant_pos]

end Ostmann.Arithmetic.HistoryPairSmoothXi

end

end OAI
