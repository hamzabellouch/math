import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualGuardedBudget
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementUncorrectedGuardedCore
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementUncorrectedSelected

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiReplacementUncorrected
open HistoryGiantXiReplacementActual
open Construction Conclusion Filter HistoryOccurrenceVariables HistoryPairPattern
open HistorySymbolicEncoding HistoryPairSmoothXi HistoryPairGiantCoordinates HistoryProductWindows
open HistoryActiveCoordinates HistorySignedResidues HistoryGiantGridCellBounds ScaleBudget

theorem selected_reference_guarded_replacement_eventually (d : Decomposition) (Bs BD Bz : ℝ)
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
    ∀ (deleted : Finset ℕ), deleted.card ≤ 2 → ∀ (hZ : 0 < logCellMass C.giantCenter deleted),
      ‖guardedPrimeDifference C s h k hs ks deleted hZ (comparisonModulus h k outside n)
        (pairModulus_dvd_comparisonModulus h k outside n)‖ ≤ 30*Real.exp (-Real.exp (giant.target*L)) ∧
      ‖guardedMixedDifference C s h k hs ks deleted hZ (comparisonModulus h k outside n)
        (pairModulus_dvd_comparisonModulus h k outside n)‖ ≤ 9*Real.exp (-Real.exp (giant.target*L)) := by
  filter_upwards [selected_reference_replacement_eventually d Bs BD Bz hBs hk₀,
    eventually_guarded_exceptional_budget d Bs BD Bz hBs hk₀,
    HistoryGiantReplacementGeometry.eventually_geometryBounds (by norm_num : (0:ℝ) < 1) 1]
    with L hun hbudget hgeometry
  intro E C hG hGu hcl hcu hb hd s outside hout houtlen l hl h k hs ks hh hk
    hsrc₁ hsrc₂ n _ hmod deleted hdeleted hZ
  have hM : 0 < comparisonModulus h k outside n := Nat.pos_of_ne_zero (NeZero.ne _)
  have hgeo := hgeometry C.blockBase C.giantCenter _ hG hcl hM hmod
  have he := hbudget E C l hl h k outside n hmod hgeo.lower_scale deleted hdeleted
  have hu := hun E C hG hGu hcl hcu hb hd s outside hout houtlen l hl h k hs ks hh hk
    hsrc₁ hsrc₂ n hmod deleted hdeleted hZ
  have hf := reference_scalar_bounds C s outside hout houtlen h k hs ks hl hh hk hsrc₁ hsrc₂
  have hg := guarded_difference_bounds C s outside hout h k hs ks hf.1 hf.2 deleted hZ
    (comparisonModulus h k outside n) (pairModulus_dvd_comparisonModulus h k outside n)
  constructor
  · calc
      _ ≤ _ := hg.1
      _ ≤ Real.exp (-Real.exp (giant.target*L))+29*Real.exp (-Real.exp (giant.target*L)) :=
        add_le_add he.1 hu.1
      _ = _ := by ring
  · calc
      _ ≤ _ := hg.2
      _ ≤ Real.exp (-Real.exp (giant.target*L))+8*Real.exp (-Real.exp (giant.target*L)) :=
        add_le_add he.2 hu.2
      _ = _ := by ring

end Ostmann.Arithmetic.HistoryGiantXiReplacementUncorrected

end

end OAI
