import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantWeightedPriorReplacementBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiPriorReplacementSamples

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantWeightedPriorReplacement
open Construction HistorySignedResidues HistoryGiantPriorGrid PrimeCellFreezing

theorem weighted_prime_sample_bound {l : ℕ} (d : Decomposition) (V : ℕ → ℕ)
    (outside : List ℕ) (h k : History l) (M : ℕ) (hd : pairModulus h k outside ∣ M)
    (hout : ∀ q ∈ outside, q.Prime) (W : ZMod M × ZMod M → ℂ)
    (BW : ℝ) (hBW : 0 ≤ BW) (hW : ∀ z, ‖W z‖ ≤ BW) (G A : ℝ) (f : (Bool → ℝ) → ℂ)
    (hA : ∀ z ∈ logRectangle (fun _ : Bool => G-1) (fun _ => G+1),
      ‖f (fun i => Real.exp (z i))‖ ≤ A)
    (p : ℕ) (hp : p ∈ logCellPrimes G) (hpw : logCellWeight G p ≠ 0)
    (q : ℕ) (hq : q ∈ logCellPrimes G) (hqw : logCellWeight G q ≠ 0) :
    ‖weightedResidueTest (residueTransform d) V outside h k M hd W (p,q) *
      f (fun t => if t then (q : ℝ) else (p : ℝ))‖ ≤
      BW*((outside.prod : ℝ)^(2^(l+1))*A) := by
  rw [weightedResidueTest, mul_assoc, norm_mul]
  exact mul_le_mul (hW _) (HistoryGiantXiPriorReplacement.prime_sample_bound
    d V outside h k M hd hout G A f hA p hp hpw q hq hqw) (norm_nonneg _) hBW

theorem weighted_mixed_sample_bound {l : ℕ} (d : Decomposition) (V : ℕ → ℕ)
    (outside : List ℕ) (h k : History l) (M : ℕ) (hd : pairModulus h k outside ∣ M)
    (hout : ∀ q ∈ outside, q.Prime) (W : ZMod M × ZMod M → ℂ)
    (BW : ℝ) (hBW : 0 ≤ BW) (hW : ∀ z, ‖W z‖ ≤ BW) (G A : ℝ) (f : (Option Unit → ℝ) → ℂ)
    (hA : ∀ z ∈ logRectangle (Option.elim' (G-1) (fun _ : Unit => G-1))
      (Option.elim' (G+1) (fun _ => G+1)), ‖f (fun i => Real.exp (z i))‖ ≤ A)
    (n : ℕ) (hn : n ∈ integerPivotCell G) (hnw : externalPivotWeight G n ≠ 0)
    (p : ℕ) (hp : p ∈ logCellPrimes G) (hpw : logCellWeight G p ≠ 0) :
    ‖weightedResidueTest (residueTransform d) V outside h k M hd W (n,p) *
      f (Option.elim' (n : ℝ) (fun _ : Unit => (p : ℝ)))‖ ≤
      BW*((outside.prod : ℝ)^(2^(l+1))*A) := by
  rw [weightedResidueTest, mul_assoc, norm_mul]
  exact mul_le_mul (hW _) (HistoryGiantXiPriorReplacement.mixed_sample_bound
    d V outside h k M hd hout G A f hA n hn hnw p hp hpw) (norm_nonneg _) hBW

end Ostmann.Arithmetic.HistoryGiantWeightedPriorReplacement

end

end OAI
