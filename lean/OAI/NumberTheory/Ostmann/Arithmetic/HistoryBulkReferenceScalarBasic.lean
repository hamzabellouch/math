import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairMixedReplacementCorrectedBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceScalar
open Construction HistoryOccurrenceVariables HistoryPairPattern HistoryPairSmoothXi HistorySymbolicEncoding
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem pairedRealXi_ne_zero_scalars (b s : ℕ) (X tb td G : ℝ)
    (h g : History l) (hs : h.Supported V outside) (gs : g.Supported V outside)
    (x : PairKey h g → ℝ)
    (hx : pairedRealXi b s X tb td G h g hs gs x ≠ 0) :
    actualRealHistoryScalar b s X tb td G outside h hs (fun i => x (leftMap h g i)) ≠ 0 ∧
    actualRealHistoryScalar b s X tb td G outside g gs (fun i => x (rightMap h g i)) ≠ 0 := by
  constructor
  · intro hz
    apply hx
    simp only [pairedRealXi,actualRealXi,hz,zero_mul]
  · intro hz
    apply hx
    simp only [pairedRealXi,actualRealXi,hz,star_zero,mul_zero]

theorem correctedPairedRealXi_ne_zero_scalars (b s : ℕ) (X tb td G : ℝ)
    (h g : History l) (hs : h.Supported V outside) (gs : g.Supported V outside)
    {τ : Type} (T U : ℝ) (Hkeys Ukeys : List (PairKey h g))
    (S : Finset τ) (cellCenter : τ → ℝ) (cellKey : τ → PairKey h g)
    (x : PairKey h g → ℝ)
    (hx : correctedPairedRealXi b s X tb td G h g hs gs T U Hkeys Ukeys S cellCenter cellKey x ≠ 0) :
    actualRealHistoryScalar b s X tb td G outside h hs (fun i => x (leftMap h g i)) ≠ 0 ∧
    actualRealHistoryScalar b s X tb td G outside g gs (fun i => x (rightMap h g i)) ≠ 0 := by
  apply pairedRealXi_ne_zero_scalars b s X tb td G h g hs gs x
  intro hz
  apply hx
  simp only [correctedPairedRealXi,hz,mul_zero]

theorem pairedRealXi_ne_zero_scalars_of_projection (b s : ℕ) (X tb td G : ℝ)
    (h g : History l) (hs : h.Supported V outside) (gs : g.Supported V outside)
    (x : PairKey h g → ℝ) (u : Key h → ℝ) (v : Key g → ℝ)
    (hu : ∀ i, x (leftMap h g i) = u i) (hv : ∀ i, x (rightMap h g i) = v i)
    (hx : pairedRealXi b s X tb td G h g hs gs x ≠ 0) :
    actualRealHistoryScalar b s X tb td G outside h hs u ≠ 0 ∧
    actualRealHistoryScalar b s X tb td G outside g gs v ≠ 0 := by
  simpa only [hu,hv] using pairedRealXi_ne_zero_scalars b s X tb td G h g hs gs x hx

end Ostmann.Arithmetic.HistoryBulkReferenceScalar

end

end OAI
