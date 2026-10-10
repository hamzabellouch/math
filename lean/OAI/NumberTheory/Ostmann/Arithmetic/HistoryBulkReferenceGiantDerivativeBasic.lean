import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkCorrectedXiBoundsZero
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantCorrectedBoundsOrder
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantCorrectedBoundsSource

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped Topology
namespace Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivative
open Filter Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistorySymbolicEncoding HistoryPairPattern HistoryPairGiantCoordinates HistoryActiveCoordinates
open HistoryBulkCorrectedXiBounds InitialCoordinatesTemplate

theorem giant_insert_right_source {l : ℕ} (h k : History l) (center : ℕ → ℝ)
    (background : PairKey h k → ℝ)
    (hs : IndependentSourceCells (independentSlot k) center (fun i => background (rightMap h k i)))
    (u : giantCoordinates h k → ℝ) :
    IndependentSourceCells (independentSlot k) center
      (fun i => insert (giantCoordinates h k) background u (rightMap h k i)) := by
  intro i q hiq hq
  cases i with
  | inl a => cases hiq
  | inr a =>
    simpa only [HistoryActiveCoordinates.insert,dite_eq_right (right_small_not_mem h k a)] using
      hs (.inr a) q hiq hq

theorem logCurve_giant_window {κ : Type*} [DecidableEq κ] (G : ℝ) (z : κ → ℝ)
    (hz : z ∈ PrimeCellFreezing.logRectangle (fun _ => G-1) (fun _ => G+1))
    (i j : κ) (t : ℝ) (ht : |t| ≤ 1) :
    |Real.log (Expr.logCurve (fun a => Real.exp (z a)) i t j)-G| ≤ 2 := by
  have hj : |z j-G| ≤ 1 := abs_le.mpr ⟨by linarith [(hz j (Set.mem_univ _)).1],
    by linarith [(hz j (Set.mem_univ _)).2]⟩
  simp only [Expr.logCurve,Real.log_mul (Real.exp_ne_zero _) (Real.exp_ne_zero _),Real.log_exp]
  by_cases he : j = i
  · simp only [ite_eq_left he]
    calc
      |z j+t-G| = |(z j-G)+t| := by congr 1; ring
      _ ≤ |z j-G|+|t| := abs_add_le _ _
      _ ≤ 2 := by linarith
  · simpa only [ite_eq_right he,add_zero] using hj.trans (by norm_num : (1:ℝ) ≤ 2)

theorem deriv_eq_zero_below_local_support (f : ℝ → ℂ) (g : ℝ → ℝ) (a : ℝ)
    (hg : ContinuousAt g 0)
    (hs : ∀ t : ℝ, |t| ≤ 1 → f t ≠ 0 → a ≤ g t) (h0 : g 0 < a) :
    deriv f 0 = 0 := by
  have ht : ∀ᶠ t : ℝ in 𝓝 0, |t| < 1 := by
    have hc : ContinuousAt (fun t : ℝ => |t|) 0 := by fun_prop
    exact hc.eventually (eventually_lt_nhds (by norm_num : |(0:ℝ)| < 1))
  have he : f =ᶠ[𝓝 0] fun _ => (0:ℂ) := by
    filter_upwards [ht,hg.eventually (eventually_lt_nhds h0)] with t ht hgt
    by_contra hn
    exact (not_le_of_gt hgt) (hs t ht.le hn)
  rw [he.deriv_eq,deriv_const]

end Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivative

end

end OAI
