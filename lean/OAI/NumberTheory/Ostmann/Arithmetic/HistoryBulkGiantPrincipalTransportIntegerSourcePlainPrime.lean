import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportPlainPrimeSource
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceSourceBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualMetadata

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport
open Construction Conclusion Filter ScaleBudget PrimeCellActualErrorBudget
open HistoryGiantWeightedPriorReplacement HistoryGiantReplacementError
open HistoryPrincipalIntegralAverage HistoryCRTIntegration ResidueHaar
open LogCellPartition HistoryGiantPriorGrid HistoryPairSmoothXi HistoryPairPattern
open HistoryPairBulkCoordinates HistoryPairGiantCoordinates HistoryBulkGiantCorrectedBounds
open HistoryGiantXiReplacementActual HistoryGiantReferenceSourceBounds HistoryGiantReferenceMean
open HistorySignedXiTransport HistorySymbolicEncoding

theorem plain_prime_integer_source_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    (hBs : 0 ≤ Bs) {k₀ : ℕ} (hk₀ : 0 < k₀) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k₀ L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
    ∀ (l s : ℕ) (outside : List ℕ)
      (_ : ∀q∈outside,0<q) (_ : outside.length=2*s) (_ : l ≤ k₀)
      (x₀ y₀ : SourceAssignment C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l))
      (s₀ t₀ P₀ Q₀ : ℤ)
      (c e : HistoryChoices C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀)
        (frequencyBound Bs BD Bz k₀ L) l)
      (_ : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l)).mass x₀ ≠ 0)
      (_ : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k₀ L/2)) k₀) l)).mass y₀ ≠ 0)
      (_ : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l c ≠ 0)
      (_ : choicesMass C.sources (Template.initial (2*(bulkSize k₀ L/2)) k₀) (frequencyBound Bs BD Bz k₀ L) l e ≠ 0)
      (_ : 0<P₀) (_ : 0<Q₀)
      (_ : |Real.log (P₀:ℝ)-(C.giantCenter:ℝ)|≤1)
      (_ : |Real.log (Q₀:ℝ)-(C.giantCenter:ℝ)|≤1),
    let seed := Template.initial (2*(bulkSize k₀ L/2)) k₀
    let V := frequencyBound Bs BD Bz k₀ L
    let T := Template.current seed l
    let h := decodeHistory C.sources seed V l (giantState (sourceState C.sources T x₀ s₀) P₀ Q₀) c
    let k := decodeHistory C.sources seed V l (giantState (sourceState C.sources T y₀ t₀) P₀ Q₀) e
    ∀ (hs : h.Supported V outside) (ks : k.Supported V outside), RootMatching h k →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (eB : ι ≃ bulkCoordinates h k) (u : ι→ℝ),
      (∀i,0<u i) →
    ∀ (M : ℕ) [NeZero M], Real.log (M:ℝ)≤Real.exp (giant.μ*L) →
    ∀ (deleted : Finset ℕ), deleted.card≤2 → ∀hZ : 0<logCellMass C.giantCenter deleted,
    ∀a : ℕ, a≤residueCostExponent k₀ → ∀R : ZMod M×ZMod M→ℂ,
      (∀z,‖R z‖≤(M:ℝ)^a) → (∑v : Bool→(ZMod M)ˣ,‖primeTest R v‖)≤(M:ℝ)^a →
    ‖guardedPeriodicSourcePrimeMean C.giantCenter deleted hZ M R
        (fun v=>jointScalar C s h k hs ks (boolEquiv h k) eB v u)-
      primeIntegral (fun _ : Bool=>C.giantCenter-1) (fun _=>C.giantCenter+1)
        (fun _=>logCellMass C.giantCenter deleted)
        (primeCutoff C.giantCenter (fun v=>jointScalar C s h k hs ks (boolEquiv h k) eB v u))*
          average (fun z : UnitPair M=>R (z.1,z.2))‖≤
      30*Real.exp (-Real.exp (giant.target*L)) := by
  filter_upwards [plain_prime_source_eventually d Bs BD Bz hBs hk₀] with L hsource
  intro E C hG hGu hcl hcu hb hd l s outside houtside hout hl x₀ y₀ s₀ t₀ P₀ Q₀ c e
    hx hy hc he hP hQ hPc hQc
  dsimp only
  intro hs ks hmatch ι _ _ eB u hu M _ hmod deleted hdeleted hZ a ha R hR hsum
  have hsrc := selected_reference_sourceBounds C (frequencyBound Bs BD Bz k₀ L) l
    x₀ y₀ s₀ t₀ c e P₀ Q₀ hx hy hc he hP hQ hPc hQc
  have hh := assigned_giant_tree_source_labels C.sources _ (frequencyBound Bs BD Bz k₀ L)
    l x₀ s₀ P₀ Q₀ c
  have hk := assigned_giant_tree_source_labels C.sources _ (frequencyBound Bs BD Bz k₀ L)
    l y₀ t₀ P₀ Q₀ e
  exact hsource E C hG hGu hcl hcu hb hd l s outside houtside hout _ _ hs ks hl hh hk
    hmatch hsrc.1 hsrc.2 ι eB u hu M hmod deleted hdeleted hZ a ha R hR hsum

end Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport

end

end OAI
