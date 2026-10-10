import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantGridCellBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualMixedCore
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualPrimeCore
import OAI.NumberTheory.Ostmann.Construction.LevelZeroFrequencySupport

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiReplacementActual
open Construction Conclusion Filter HistoryOccurrenceVariables HistoryPairPattern
open HistorySymbolicEncoding HistoryPairSmoothXi HistoryPairGiantCoordinates HistoryProductWindows
open HistoryActiveCoordinates HistorySignedResidues HistoryGiantGridCellBounds ScaleBudget

theorem selected_reference_replacement_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    (hBs : 0 ≤ Bs) {k₀ : ℕ} (hk₀ : 0 < k₀) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k₀ L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
    ∀ (s : ℕ) (outside : List ℕ), (∀ q ∈ outside, q.Prime) → outside.length = 2*s →
    ∀ (l : ℕ), l < k₀ → ∀ (h k : History l)
      (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
      (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside),
      TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) h →
      TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) k → RootGiantsAgree h k →
      SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
        h (leftMap h k) (giantCoordinates h k) (pairBackground h k)
        (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1) →
      SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
        k (rightMap h k) (giantCoordinates h k) (pairBackground h k)
        (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1) →
      pairedRealXi (bulkSize k₀ L/2) s C.scale C.bulkBin C.spectatorBin C.giantCenter
        h k hs ks (pairBackground h k) ≠ 0 →
    ∀ (n : ℕ) [NeZero (comparisonModulus h k outside n)],
      Real.log (comparisonModulus h k outside n:ℝ) ≤ Real.exp (giant.μ*L) →
    ∀ (deleted : Finset ℕ), deleted.card ≤ 2 → ∀ (hZ : 0 < logCellMass C.giantCenter deleted),
      ‖primeDifference C s h k hs ks deleted hZ (comparisonModulus h k outside n)
        (pairModulus_dvd_comparisonModulus h k outside n)‖ ≤ 29*Real.exp (-Real.exp (giant.target*L)) ∧
      ‖mixedDifference C s h k hs ks deleted hZ (comparisonModulus h k outside n)
        (pairModulus_dvd_comparisonModulus h k outside n)‖ ≤ 8*Real.exp (-Real.exp (giant.target*L)) := by
  obtain ⟨δp,Kp,Lp,hδp,hKp,hLp,hprime⟩ := exists_prime_replacement_core
  obtain ⟨δm,Km,Lm,hδm,hKm,hLm,hmixed⟩ := exists_mixed_replacement_core
  filter_upwards [selected_gridCellBounds_eventually d Bs BD Bz hk₀ hKp.le hδp Lp,
    selected_gridCellBounds_eventually d Bs BD Bz hk₀ hKm.le hδm Lm,
    eventually_actual_error_bounds d Bs BD Bz hBs hk₀ hKp.le hδp,
    eventually_actual_error_bounds d Bs BD Bz hBs hk₀ hKm.le hδm] with L hgp hgm hep hem
  intro E C hG hGu hcl hcu hb hd s outside hout houtlen l hl h k hs ks hh hk hgiants
    hsrc₁ hsrc₂ hne n _ hmod deleted hdeleted hZ
  have hM : 0 < comparisonModulus h k outside n := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain ⟨hgeop,hbp⟩ := hgp E C hG hGu hcl hcu hb hd _ hM hmod
  obtain ⟨hgeom,hbm⟩ := hgm E C hG hGu hcl hcu hb hd _ hM hmod
  have hpb := (hbp deleted hdeleted).1
  have hmb := (hbm deleted hdeleted).1
  have hX : 0 < (C.scale:ℝ) := by exact_mod_cast InitialEta.initial_scale_pos C
  refine ⟨?_,?_⟩
  · exact (hprime C s outside hX hout houtlen h k hs ks hl hh hk hgiants hsrc₁ hsrc₂ hne
      deleted hZ _ (pairModulus_dvd_comparisonModulus h k outside n) hgeop hpb).trans
      (hep E C l hl.le h k hh hk outside hout deleted hdeleted n hmod hgeop.lower_scale Lp hpb).1
  · exact (hmixed C s outside hX hout houtlen h k hs ks hl hh hk hgiants hsrc₁ hsrc₂ hne
      deleted hZ _ (pairModulus_dvd_comparisonModulus h k outside n) hgeom hmb).trans
      (hem E C l hl.le h k hh hk outside hout deleted hdeleted n hmod hgeom.lower_scale Lm hmb).2

end Ostmann.Arithmetic.HistoryGiantXiReplacementActual

end

end OAI
