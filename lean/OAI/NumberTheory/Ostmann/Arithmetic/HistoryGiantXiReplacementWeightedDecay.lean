import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementWeightedBudget
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementWeightedGuardedSelected

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiReplacementWeighted
open HistoryGiantXiReplacementActual
open Construction Conclusion Filter HistoryOccurrenceVariables HistoryPairPattern
open HistorySymbolicEncoding HistoryPairSmoothXi HistoryPairGiantCoordinates HistoryProductWindows
open HistoryActiveCoordinates HistorySignedResidues HistoryGiantGridCellBounds ScaleBudget

theorem selected_reference_guarded_decay_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    (hBs : 0 ≤ Bs) {k₀ : ℕ} (hk₀ : 0 < k₀) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k₀ L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
    ∀ (s : ℕ) (outside : List ℕ), (∀ q ∈ outside, q.Prime) → outside.length = 2*s →
    ∀ (l : ℕ), l ≤ k₀ → ∀ (h k : History l)
      (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
      (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside),
      TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) h →
      TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) k →
      SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
        h (leftMap h k) (giantCoordinates h k) (pairBackground h k)
        (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1) →
      SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
        k (rightMap h k) (giantCoordinates h k) (pairBackground h k)
        (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1) →
    ∀ (n : ℕ) [NeZero (comparisonModulus h k outside n)],
      Real.log (comparisonModulus h k outside n:ℝ) ≤ Real.exp (giant.μ*L) →
    ∀ (deleted : Finset ℕ), deleted.card ≤ 2 → ∀ (hZ : 0 < logCellMass C.giantCenter deleted)
      (W : ZMod (comparisonModulus h k outside n) × ZMod (comparisonModulus h k outside n) → ℂ)
, (∀ z, ‖W z‖ ≤ (comparisonModulus h k outside n:ℝ)) →
      ‖guardedPrimeDifference C s h k hs ks deleted hZ (comparisonModulus h k outside n)
        (pairModulus_dvd_comparisonModulus h k outside n) W‖ ≤ 30*Real.exp (-Real.exp ((1/80:ℝ)*L)) ∧
      ‖guardedMixedDifference C s h k hs ks deleted hZ (comparisonModulus h k outside n)
        (pairModulus_dvd_comparisonModulus h k outside n) W‖ ≤ 9*Real.exp (-Real.exp ((1/80:ℝ)*L)) := by
  filter_upwards [selected_reference_guarded_replacement_eventually d Bs BD Bz hBs hk₀,
    eventually_weighted_modulus_error] with L hr hbudget
  intro E C hG hGu hcl hcu hb hd s outside hout houtlen l hl h k hs ks hh hk
    hsrc₁ hsrc₂ n _ hmod deleted hdeleted hZ W hW
  have hM : 0 < comparisonModulus h k outside n := Nat.pos_of_ne_zero (NeZero.ne _)
  have hsave := hbudget _ hM hmod
  have hraw := hr E C hG hGu hcl hcu hb hd s outside hout houtlen l hl h k hs ks hh hk
    hsrc₁ hsrc₂ n hmod deleted hdeleted hZ W (comparisonModulus h k outside n) (by positivity) hW
  constructor
  · apply hraw.1.trans
    nlinarith [mul_le_mul_of_nonneg_left hsave (by norm_num : (0:ℝ) ≤ 30)]
  · apply hraw.2.trans
    nlinarith [mul_le_mul_of_nonneg_left hsave (by norm_num : (0:ℝ) ≤ 9)]

end Ostmann.Arithmetic.HistoryGiantXiReplacementWeighted

end

end OAI
