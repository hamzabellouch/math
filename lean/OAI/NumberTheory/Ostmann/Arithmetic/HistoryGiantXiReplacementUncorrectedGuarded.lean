import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantIndependentModulus
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualMetadata
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementUncorrectedGuardedComparison
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementUncorrectedGuardedSelected

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiReplacementUncorrected
open HistoryGiantXiReplacementActual
open Construction Conclusion Filter HistoryOccurrenceVariables HistoryPairPattern
open HistorySymbolicEncoding HistoryPairSmoothXi HistoryPairGiantCoordinates HistoryProductWindows
open HistoryActiveCoordinates HistorySignedResidues ScaleBudget HistoryGiantReferenceMean
open HistoryGiantReferenceSourceBounds HistoryGiantIndependentModulus HistorySignedXiTransport

theorem selected_integer_guarded_replacement_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    (hBs : 0 ≤ Bs) {k₀ : ℕ} (hk₀ : 0 < k₀) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k₀ L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
    ∀ spectator : PrimeSource,
      (∀ p : spectator.Sample, Real.log (p:ℕ) ≤ Real.exp ((1/1000:ℝ)*L)) →
    ∀ ds : Fin (2*(bulkSize k₀ L/2)) → spectator.Sample,
    let outside := spectatorList spectator ds
    ∀ l ≤ k₀,
    let seed := Template.initial (2*(bulkSize k₀ L/2)) k₀
    let V := frequencyBound Bs BD Bz k₀ L
    let T := Template.current seed l
    ∀ (x y : SourceAssignment C.sources T) (s t P Q : ℤ)
      (c e : HistoryChoices C.sources seed V l),
      (assignmentPrior C.sources T).mass x ≠ 0 → (assignmentPrior C.sources T).mass y ≠ 0 →
      choicesMass C.sources seed V l c ≠ 0 → choicesMass C.sources seed V l e ≠ 0 →
      0 < P → 0 < Q → |Real.log (P:ℝ)-(C.giantCenter:ℝ)| ≤ 1 →
      |Real.log (Q:ℝ)-(C.giantCenter:ℝ)| ≤ 1 →
    let h := decodeHistory C.sources seed V l (giantState (sourceState C.sources T x s) P Q) c
    let g := decodeHistory C.sources seed V l (giantState (sourceState C.sources T y t) P Q) e
    ∀ (hs : h.Supported V outside) (gs : g.Supported V outside)
      (hout : ∀ q ∈ outside, q.Prime),
    ∀ (deleted : Finset ℕ), deleted.card ≤ 2 → ∀ (hZ : 0 < logCellMass C.giantCenter deleted),
      ‖comparisonGuardedPrimeDifference C (bulkSize k₀ L/2) h g hs gs hout deleted hZ (k₀+2)‖ ≤
        30*Real.exp (-Real.exp (giant.target*L)) ∧
      ‖comparisonGuardedMixedDifference C (bulkSize k₀ L/2) h g hs gs hout deleted hZ (k₀+2)‖ ≤
        9*Real.exp (-Real.exp (giant.target*L)) := by
  filter_upwards [selected_reference_guarded_replacement_eventually d Bs BD Bz hBs hk₀,
    selected_integer_comparisonModulus_cap_eventually d Bs BD Bz hk₀] with L hr hcap
  intro E C hG hGu hcl hcu hb hd spectator hspec ds
  dsimp only
  intro l hl x y s t P Q c e hx hy hc he hP hQ hPc hQc hs gs hout deleted hdeleted hZ
  have hinfo := hcap E C hG hcl hcu hb hd spectator hspec ds l hl
    x y s t P Q c e hx hy hc he hs gs
  have hmod : Real.log (comparisonModulus
      (decodeHistory C.sources _ _ l (giantState (sourceState C.sources _ x s) P Q) c)
      (decodeHistory C.sources _ _ l (giantState (sourceState C.sources _ y t) P Q) e)
      (spectatorList spectator ds) (k₀+2):ℝ) ≤ Real.exp (giant.μ*L) := by
    simpa only [giant,show (12/1000:ℝ) = 3/250 by norm_num] using hinfo.2.1
  let : NeZero (comparisonModulus
      (decodeHistory C.sources _ _ l (giantState (sourceState C.sources _ x s) P Q) c)
      (decodeHistory C.sources _ _ l (giantState (sourceState C.sources _ y t) P Q) e)
      (spectatorList spectator ds) (k₀+2)) := ⟨hinfo.1.ne'⟩
  have hsource := selected_reference_sourceBounds C (frequencyBound Bs BD Bz k₀ L) l
    x y s t c e P Q hx hy hc he hP hQ hPc hQc
  have hh := assigned_giant_tree_source_labels C.sources _ (frequencyBound Bs BD Bz k₀ L)
    l x s P Q c
  have hg := assigned_giant_tree_source_labels C.sources _ (frequencyBound Bs BD Bz k₀ L)
    l y t P Q e
  have hlen : (spectatorList spectator ds).length = 2*(bulkSize k₀ L/2) := by
    simp only [spectatorList,List.length_ofFn]
  simpa only [comparisonGuardedPrimeDifference,comparisonGuardedMixedDifference] using
    hr E C hG hGu hcl hcu hb hd (bulkSize k₀ L/2) (spectatorList spectator ds) hout hlen
      l hl _ _ hs gs hh hg hsource.1 hsource.2 (k₀+2) hmod deleted hdeleted hZ

end Ostmann.Arithmetic.HistoryGiantXiReplacementUncorrected

end

end OAI
