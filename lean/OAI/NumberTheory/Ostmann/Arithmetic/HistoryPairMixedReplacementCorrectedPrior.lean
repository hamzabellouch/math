import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairMixedReplacementCorrectedDiagonal
import OAI.NumberTheory.Ostmann.Construction.GiantCellPriorIdentity

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairSmoothXi
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistoryPairPattern HistorySymbolicEncoding InitialCoordinatesTemplate HistoryActiveCoordinates
open scoped BigOperators
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

def rootPrimePriorCutoff (h k : History l) (G : ℝ) (roots : List Bool) (x : PairKey h k → ℝ) : ℝ :=
  ∏i : Fin roots.length,giantCell G (x (leftMap h k (.inl (roots.get i))))

def priorCellCenter {τ : Type} (center : τ → ℝ) (G : ℝ) (roots : List Bool) : τ ⊕ Fin roots.length → ℝ :=
  Sum.elim center (fun _ => G)

def priorCellKey {τ : Type} (h k : History l) (cellKey : τ → PairKey h k) (roots : List Bool) :
    τ ⊕ Fin roots.length → PairKey h k :=
  Sum.elim cellKey (fun i => leftMap h k (.inl (roots.get i)))

theorem rootCounterpart_prior_cells {τ : Type} [Fintype τ]
    (h k : History l) (T U G : ℝ) (Hkeys Ukeys : List (PairKey h k))
    (cellCenter : τ → ℝ) (cellKey : τ → PairKey h k) (roots : List Bool) (x : PairKey h k → ℝ) :
    rootCounterpart T U Hkeys Ukeys (Finset.univ : Finset (τ ⊕ Fin roots.length))
      (priorCellCenter cellCenter G roots) (priorCellKey h k cellKey roots) x =
    rootPrimePriorCutoff h k G roots x * rootCounterpart T U Hkeys Ukeys Finset.univ cellCenter cellKey x := by
  simp only [rootCounterpart,counterpartArchimedean,Fintype.prod_sum_type,
    priorCellCenter,priorCellKey,Sum.elim_inl,Sum.elim_inr,rootPrimePriorCutoff]
  ring

theorem correctedPairedRealXi_prior_cells {τ : Type} [Fintype τ]
    (b s : ℕ) (X tb td G : ℝ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (T U : ℝ) (Hkeys Ukeys : List (PairKey h k))
    (cellCenter : τ → ℝ) (cellKey : τ → PairKey h k) (roots : List Bool) (x : PairKey h k → ℝ) :
    correctedPairedRealXi b s X tb td G h k hs ks T U Hkeys Ukeys
      (Finset.univ : Finset (τ ⊕ Fin roots.length))
      (priorCellCenter cellCenter G roots) (priorCellKey h k cellKey roots) x =
    (rootPrimePriorCutoff h k G roots x : ℂ) *
      correctedPairedRealXi b s X tb td G h k hs ks T U Hkeys Ukeys Finset.univ cellCenter cellKey x := by
  simp only [correctedPairedRealXi,rootCounterpart_prior_cells,Complex.ofReal_mul,mul_assoc]

theorem correctedPairedRealXi_prior_only (b s : ℕ) (X tb td G : ℝ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (roots : List Bool) (x : PairKey h k → ℝ) :
    correctedPairedRealXi b s X tb td G h k hs ks 0 0 [] []
      (Finset.univ : Finset (Fin roots.length)) (fun _ => G)
      (fun i => leftMap h k (.inl (roots.get i))) x =
    (rootPrimePriorCutoff h k G roots x : ℂ) * pairedRealXi b s X tb td G h k hs ks x := by
  simp only [correctedPairedRealXi,rootCounterpart,counterpartArchimedean,List.map_nil,List.prod_nil,
    Real.exp_zero,div_one,one_mul,rootPrimePriorCutoff]

theorem rootPrimePriorCutoff_singleton (h k : History l) (G : ℝ) (a : Bool) (x : PairKey h k → ℝ) :
    rootPrimePriorCutoff h k G [a] x = giantCell G (x (leftMap h k (.inl a))) := by
  simp [rootPrimePriorCutoff]

theorem rootPrimePriorCutoff_both (h k : History l) (G : ℝ) (x : PairKey h k → ℝ) :
    rootPrimePriorCutoff h k G [false,true] x =
      giantCell G (x (leftMap h k (.inl false))) * giantCell G (x (leftMap h k (.inl true))) := by
  simp [rootPrimePriorCutoff,Fin.prod_univ_two]

end Ostmann.Arithmetic.HistoryPairSmoothXi

end

end OAI
