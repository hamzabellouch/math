import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualBoundsBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualGuardedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualMetadata
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualSource

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiReplacementActual
open Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern
open HistorySymbolicEncoding HistoryPairSmoothXi HistoryPairGiantCoordinates HistoryProductWindows
open HistoryGiantXiPriorReplacement HistoryActiveCoordinates HistorySignedResidues
open HistoryGiantPriorGrid PrimeCellFreezing LogCellPartition HistoryGiantReferenceSourceBounds

theorem reference_scalar_bounds
    {d : Decomposition} {Bs BD Bz L : ℝ} {k₀ l : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k₀ L E) (s : ℕ) (outside : List ℕ)
    (hout : ∀ q ∈ outside, q.Prime) (houtlen : outside.length = 2*s)
    (h k : History l) (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (hl : l < k₀) (hh : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) h)
    (hk : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) k)
    (hgiants : RootGiantsAgree h k)
    (hsrc₁ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      h (leftMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    (hsrc₂ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      k (rightMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    (hne : pairedRealXi (bulkSize k₀ L/2) s C.scale C.bulkBin C.spectatorBin C.giantCenter
      h k hs ks (pairBackground h k) ≠ 0) :
    (∀ z ∈ logRectangle (fun _ : Bool => C.giantCenter-1) (fun _ => C.giantCenter+1),
      ‖primeScalar C s h k hs ks (fun i => Real.exp (z i))‖ ≤
        referenceAmplitude (Bs:=Bs) (k₀:=k₀) (L:=L) l) ∧
    (∀ z ∈ logRectangle (Option.elim' (C.giantCenter-1) (fun _ : Unit => C.giantCenter-1))
      (Option.elim' (C.giantCenter+1) (fun _ : Unit => C.giantCenter+1)),
      ‖mixedScalar C s h k hs ks (fun i => Real.exp (z i))‖ ≤
        referenceAmplitude (Bs:=Bs) (k₀:=k₀) (L:=L) l) := by
  have hX : 0 < (C.scale:ℝ) := by exact_mod_cast InitialEta.initial_scale_pos C
  have hp : ∀ q ∈ outside, 0 < q := fun q hq => (hout q hq).pos
  have hcorr := reference_counterpartBounds C s h k hs ks hl hk hgiants hsrc₂ hne
  have hbound {ι : Type} [Fintype ι] [DecidableEq ι] (eqv : ι ≃ giantCoordinates h k) := corrected_rectangle_bounds (bulkSize k₀ L/2) s k₀ C.scale C.bulkBin C.spectatorBin
    C.giantCenter (initialGap Bs k₀ L) (2+2*(k₀:ℝ)) (C.cells.center (bulkSize k₀ L/2))
    hX hp houtlen h k hs ks hl.le hh hk
    ((C.giantCenter:ℝ)+C.compensationLogScale l+stepGap BD Bz k₀ L l) (C.compensationLogScale l)
    (nominalInheritedWidth k₀ l+2) (nominalRemovedWidth k₀ l)
    (pairedDiagonalHKeys h k (l+1)) (pairedDiagonalUKeys h k (l+1))
    (Finset.univ : Finset (Fin (diagonalCellKeys k (l+1)).length))
    (pairedDiagonalCellCenter k (l+1) C.giantCenter (C.cells.center (bulkSize k₀ L/2)))
    (pairedDiagonalCellKey h k (l+1)) (giantCoordinates h k) (pairBackground h k) eqv
  have hb := hbound (boolEquiv h k) (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1)
    hsrc₁ hsrc₂ hcorr (selected_Xi_source_center C)
  have hm := hbound (optionEquiv h k) (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1)
    hsrc₁ hsrc₂ hcorr (selected_Xi_source_center C)
  refine ⟨hb.2.2,?_⟩
  have he (a : ℝ) : Option.elim' a (fun _ : Unit => a) = (fun _ : Option Unit => a) := by
    funext i
    cases i <;> rfl
  rw [he,he]
  exact hm.2.2

theorem guarded_difference_bounds
    {d : Decomposition} {Bs BD Bz L : ℝ} {k₀ l : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k₀ L E) (s : ℕ) (outside : List ℕ)
    (hout : ∀ q ∈ outside, q.Prime) (h k : History l)
    (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (hprime : ∀ z ∈ logRectangle (fun _ : Bool => C.giantCenter-1) (fun _ => C.giantCenter+1),
      ‖primeScalar C s h k hs ks (fun i => Real.exp (z i))‖ ≤ referenceAmplitude (Bs:=Bs) (k₀:=k₀) (L:=L) l)
    (hmixed : ∀ z ∈ logRectangle (Option.elim' (C.giantCenter-1) (fun _ : Unit => C.giantCenter-1))
      (Option.elim' (C.giantCenter+1) (fun _ : Unit => C.giantCenter+1)),
      ‖mixedScalar C s h k hs ks (fun i => Real.exp (z i))‖ ≤ referenceAmplitude (Bs:=Bs) (k₀:=k₀) (L:=L) l)
    (deleted : Finset ℕ) (hZ : 0 < logCellMass C.giantCenter deleted)
    (M : ℕ) [NeZero M] (hd : pairModulus h k outside ∣ M) :
    ‖guardedPrimeDifference C s h k hs ks deleted hZ M hd‖ ≤
      ((outside.prod:ℝ)^(2^(l+1))*referenceAmplitude (Bs:=Bs) (k₀:=k₀) (L:=L) l)*
        (Real.exp (1-C.giantCenter)/logCellMass C.giantCenter deleted)+
      ‖primeDifference C s h k hs ks deleted hZ M hd‖ ∧
    ‖guardedMixedDifference C s h k hs ks deleted hZ M hd‖ ≤
      ((outside.prod:ℝ)^(2^(l+1))*referenceAmplitude (Bs:=Bs) (k₀:=k₀) (L:=L) l)*
        (8*Real.exp (-C.giantCenter))+
      ‖mixedDifference C s h k hs ks deleted hZ M hd‖ := by
  have hp := guardedSourcePrimeMean_error d (frequencyBound Bs BD Bz k₀ L) outside h k
    C.giantCenter deleted hZ M hd hout (primeScalar C s h k hs ks)
    (referenceAmplitude_nonneg Bs L k₀ l) hprime
  have hm := guardedSourceMixedMean_error d (frequencyBound Bs BD Bz k₀ L) outside h k
    C.giantCenter deleted hZ M hd hout (mixedScalar C s h k hs ks)
    (referenceAmplitude_nonneg Bs L k₀ l) hmixed
  constructor
  · exact (norm_sub_le_norm_sub_add_norm_sub _ (sourcePrimeMean (residueTransform d) (frequencyBound Bs BD Bz k₀ L)
      outside h k C.giantCenter deleted hZ M hd (primeScalar C s h k hs ks)) _).trans
      (add_le_add hp le_rfl)
  · exact (norm_sub_le_norm_sub_add_norm_sub _ (sourceMixedMean (residueTransform d) (frequencyBound Bs BD Bz k₀ L)
      outside h k C.giantCenter deleted hZ M hd (mixedScalar C s h k hs ks)) _).trans
      (add_le_add hm le_rfl)

end Ostmann.Arithmetic.HistoryGiantXiReplacementActual

end

end OAI
