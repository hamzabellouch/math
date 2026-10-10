import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorGridMixed
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorGridPrime
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairGiantCoordinates
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairMixedReplacementCorrectedPrior
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairMixedReplacementCorrectedReindex

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiPriorReplacement
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistoryPairPattern HistorySymbolicEncoding HistoryActiveCoordinates
open HistoryPairSmoothXi HistoryPairGiantCoordinates HistoryGiantPriorGrid
open PrimeCellFreezing InitialCoordinatesTemplate
open scoped ContDiff BigOperators
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem primeCutoff_corrected (b s : ℕ) (X tb td G : ℝ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    {τ : Type} [Fintype τ] (T U : ℝ) (Hkeys Ukeys : List (PairKey h k))
    (cellCenter : τ → ℝ) (cellKey : τ → PairKey h k) :
    primeCutoff G (reindexedCorrectedRealXi b s X tb td G h k hs ks T U Hkeys Ukeys
      Finset.univ cellCenter cellKey (giantCoordinates h k) (pairBackground h k) (boolEquiv h k)) =
    reindexedCorrectedRealXi b s X tb td G h k hs ks T U Hkeys Ukeys
      (Finset.univ : Finset (τ ⊕ Fin ([false,true] : List Bool).length))
      (priorCellCenter cellCenter G [false,true]) (priorCellKey h k cellKey [false,true])
      (giantCoordinates h k) (pairBackground h k) (boolEquiv h k) := by
  funext x
  unfold primeCutoff reindexedCorrectedRealXi
  rw [correctedPairedRealXi_prior_cells, rootPrimePriorCutoff_both]
  rw [Complex.ofReal_mul]
  change _ = (giantCell G (insertGiants h k x (leftMap h k (.inl false))) : ℂ) *
    (giantCell G (insertGiants h k x (leftMap h k (.inl true))) : ℂ) * _
  rw [insertGiants_giant, insertGiants_giant]

theorem mixedCutoff_corrected (b s : ℕ) (X tb td G : ℝ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    {τ : Type} [Fintype τ] (T U : ℝ) (Hkeys Ukeys : List (PairKey h k))
    (cellCenter : τ → ℝ) (cellKey : τ → PairKey h k)
    (x : Option Unit → ℝ) (hx : 0 < x (some ())) :
    mixedGiantPrimeTest G (reindexedCorrectedRealXi b s X tb td G h k hs ks T U Hkeys Ukeys
      Finset.univ cellCenter cellKey (giantCoordinates h k) (pairBackground h k) (optionEquiv h k)) x =
    reindexedCorrectedRealXi b s X tb td G h k hs ks T U Hkeys Ukeys
      (Finset.univ : Finset (τ ⊕ Fin ([true] : List Bool).length))
      (priorCellCenter cellCenter G [true]) (priorCellKey h k cellKey [true])
      (giantCoordinates h k) (pairBackground h k) (optionEquiv h k) x := by
  unfold mixedGiantPrimeTest reindexedCorrectedRealXi
  rw [correctedPairedRealXi_prior_cells, rootPrimePriorCutoff_singleton]
  have he : insert (giantCoordinates h k) (pairBackground h k)
      (fun j => x ((optionEquiv h k).symm j)) (leftMap h k (.inl true)) = x (some ()) := by
    change insert (giantCoordinates h k) (pairBackground h k)
      (fun j => x ((optionEquiv h k).symm j)) (optionEquiv h k (some ())).val = _
    rw [HistoryActiveCoordinates.insert, dite_eq_left (optionEquiv h k (some ())).property]
    change x ((optionEquiv h k).symm (optionEquiv h k (some ()))) = x (some ())
    rw [Equiv.symm_apply_apply]
  rw [he, giantCell_of_pos G hx]

theorem background_positive {b k₀ : ℕ} {G : ℝ} {center : ℕ → ℝ}
    (h k : History l) (I : Finset (PairKey h k)) (background : PairKey h k → ℝ)
    (lo hi : I → ℝ)
    (hh : SourceBounds b k₀ G center h (leftMap h k) I background lo hi)
    (hk : SourceBounds b k₀ G center k (rightMap h k) I background lo hi) :
    ∀ i, 0 < background i := by
  intro i
  obtain ⟨j,rfl⟩ := unionMap_surjective h k i
  rcases j with j | j
  · exact hh.background_source.positive j
  · exact hk.background_source.positive j

theorem corrected_rectangle_bounds (b s k₀ : ℕ) (X tb td G Δ E : ℝ)
    (center : ℕ → ℝ) (hX : 0 < X) (houtside : ∀ q ∈ outside, 0 < q)
    (hout : outside.length = 2*s) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hlk : l ≤ k₀) (hl₁ : TreeSourceLabels (Template.initial (2*b) k₀) h)
    (hl₂ : TreeSourceLabels (Template.initial (2*b) k₀) k)
    {τ : Type} (T U WH Wu : ℝ) (Hkeys Ukeys : List (PairKey h k))
    (S : Finset τ) (cellCenter : τ → ℝ) (cellKey : τ → PairKey h k)
    (I : Finset (PairKey h k)) (background : PairKey h k → ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι ≃ I) (lo hi : ι → ℝ)
    (hsrc₁ : SourceBounds b k₀ G center h (leftMap h k) I background
      (fun j => lo (e.symm j)) (fun j => hi (e.symm j)))
    (hsrc₂ : SourceBounds b k₀ G center k (rightMap h k) I background
      (fun j => lo (e.symm j)) (fun j => hi (e.symm j)))
    (hcorr : CounterpartBounds T U WH Wu Hkeys Ukeys I background
      (fun j => lo (e.symm j)) (fun j => hi (e.symm j)))
    (hcenter : Real.log X+Δ-E ≤ 2*G+2*tb+2*td+
      (∑ a,∑ i,topCenters b center a i)+
      (∑ a,∑ j : Fin k₀,∑ i,compensationCenters b center a j i)) :
    let f := reindexedCorrectedRealXi b s X tb td G h k hs ks T U Hkeys Ukeys
      S cellCenter cellKey I background e
    ContDiff ℝ ∞ (fun z : ι → ℝ => f (fun i => Real.exp (z i))) ∧
    (∀ z ∈ logRectangle lo hi, ∀ i,
      ‖deriv (fun t => f (Expr.logCurve (fun q => Real.exp (z q)) i t)) 0‖ ≤
        correctedPairDerivativeBound WH Wu Hkeys.length Ukeys.length S.card h k V b k₀ tb Δ E center) ∧
    (∀ z ∈ logRectangle lo hi, ‖f (fun i => Real.exp (z i))‖ ≤
      Real.exp (WH+Wu)*Real.exp (-((2^l : ℕ) : ℝ)*Δ+sourceXiConstant l k₀ E)) := by
  have hbackground := background_positive h k I background _ _ hsrc₁ hsrc₂
  refine ⟨reindexedCorrectedRealXi_log_contDiff b s X tb td G hX houtside h k hs ks
    T U Hkeys Ukeys S cellCenter cellKey I background hbackground e, ?_, ?_⟩
  · intro z hz i
    have hh := hcorr.log_products hbackground _ (reindex_mem_logRectangle e lo hi z hz)
    exact reindexedCorrectedRealXi_deriv_le b s k₀ X tb td G Δ E center hX houtside hout h k hs ks
      hlk hl₁ hl₂ T U WH Wu Hkeys Ukeys S cellCenter cellKey I background hbackground e _ i
      (fun _ => Real.exp_pos _) hh.1 hh.2
      (hsrc₁.sourceDomain _ (reindex_mem_logRectangle e lo hi z hz))
      (hsrc₂.sourceDomain _ (reindex_mem_logRectangle e lo hi z hz)) hcenter
  · intro z hz
    have hh := hcorr.log_products hbackground _ (reindex_mem_logRectangle e lo hi z hz)
    exact correctedPairedRealXi_norm_le b s k₀ X tb td G Δ E center hX houtside hout h k hs ks
      T U WH Wu Hkeys Ukeys S cellCenter cellKey _
      (insert_positive I background _ hbackground (fun _ => Real.exp_pos _)) hh.1 hh.2
      (hsrc₁.sourceDomain _ (reindex_mem_logRectangle e lo hi z hz))
      (hsrc₂.sourceDomain _ (reindex_mem_logRectangle e lo hi z hz)) hcenter

end Ostmann.Arithmetic.HistoryGiantXiPriorReplacement

end

end OAI
