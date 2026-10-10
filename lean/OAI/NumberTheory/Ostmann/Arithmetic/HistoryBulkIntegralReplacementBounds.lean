import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIntegralReplacementBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkIntegralReplacement
open Construction Conclusion HistoryBulkPriorGrid HistoryPrincipalIntegralAverage
open HistoryPrincipalIntegralFinite HistoryBulkReplacementError PrimeCellFreezing ScaleBudget Filter
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure BulkBounds (k : ℕ) (L C : ℝ) (f : (ι→ℝ)→ℂ) : Prop where
  differentiable : ∀z∈logRectangle (fun _ : ι=>bulkLogLower L) (fun _=>bulkLogUpper L),
    DifferentiableAt ℝ (fun y=>f (fun i=>Real.exp (y i))) z
  derivative : ∀z∈logRectangle (fun _ : ι=>bulkLogLower L) (fun _=>bulkLogUpper L),∀i,
    ‖deriv (fun t=>f (Characters.RationalHistory.Expr.logCurve (fun q=>Real.exp (z q)) i t)) 0‖ ≤
      Real.exp (C*((bulkSize k L:ℝ)+1))
  norm : ∀z∈logRectangle (fun _ : ι=>bulkLogLower L) (fun _=>bulkLogUpper L),
    ‖f (fun i=>Real.exp (z i))‖ ≤ Real.exp (C*((bulkSize k L:ℝ)+1))

def bulkMain (L : ℝ) (E : Finset ℕ) {M : ℕ} [NeZero M]
    (F : (ι→(ZMod M)ˣ)→ℂ) (f : (ι→ℝ)→ℂ) : ℂ :=
  primeIntegral (fun _ : ι=>bulkLogLower L) (fun _=>bulkLogUpper L)
    (fun _=>bulkNormalizer L E) f * ResidueHaar.average F

theorem sourceBulkMean_average_replacement_eventually (k : ℕ) (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀(ι:Type*) [Fintype ι] [DecidableEq ι],
      ∀(M:ℕ) [NeZero M], ∀(a:ℕ)(E:Finset ℕ),
      Fintype.card ι ≤ 2^k*bulkSize k L → a ≤ residueCostExponent k →
      Real.log (M:ℝ) ≤ Real.exp (bulk.μ*L) → E.card ≤ 2 →
      ∀(hZ:0 < harmonicPrimeMass (bulkPrimeBand L E))
        (hsize:(M:ℝ) < Real.exp (bulkLogLower L))
        (F:(ι→(ZMod M)ˣ)→ℂ)(f:(ι→ℝ)→ℂ),
      (∑u:ι→(ZMod M)ˣ,‖F u‖) ≤ (M:ℝ)^(Fintype.card ι+a) →
      BulkBounds k L C f →
      ‖sourceBulkMean L E hZ M hsize F f-bulkMain L E F f‖ ≤
        3*Real.exp (-Real.exp (bulk.target*L)) := by
  filter_upwards [sourceBulkMean_replacement_eventually k C] with L hL
  intro ι _ _ M _ a E hn ha hm hE hZ hsize F f hF hf
  simpa only [principalIntegral_mul_sum,bulkMain] using
    hL ι M a E hn ha hm hE hZ hsize F f hF hf.differentiable hf.derivative hf.norm

end Ostmann.Arithmetic.HistoryBulkIntegralReplacement

end

end OAI
