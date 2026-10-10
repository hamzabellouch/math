import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorCollision
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceMeanNonzeroOriginal
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairGiantCoordinates

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryGiantReferenceMean
open Construction HistorySignedResidues HistoryPairSmoothXi HistoryPairGiantCoordinates
open HistoryGiantPriorGrid
variable {l : ℕ} (d : Decomposition) (V : ℕ→ℕ) (outside : List ℕ)
variable (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
variable (n b s : ℕ) (X tb td G : ℝ)

theorem referenceTerm_eq_bool (P Q : ℤ) :
    referenceTerm d V outside h k hs ks n b s X tb td G P Q=
      ((h.compensationProduct:ℂ)*(k.compensationProduct:ℂ))*
        (if Nat.Coprime P.natAbs Q.natAbs then
          liftedResidueTest (residueTransform d) V outside h k (comparisonModulus h k outside n)
            (pairModulus_dvd_comparisonModulus h k outside n) (P,Q)*
          reindexedRealXi b s X tb td G h k hs ks (giantCoordinates h k) (pairBackground h k)
            (boolEquiv h k) (fun t=>if t then (Q:ℝ) else (P:ℝ)) else 0) := by
  rw [reindexedRealXi_bool_signed]
  unfold referenceTerm
  split_ifs <;> ring

theorem referenceTerm_eq_option (P Q : ℤ) :
    referenceTerm d V outside h k hs ks n b s X tb td G P Q=
      ((h.compensationProduct:ℂ)*(k.compensationProduct:ℂ))*
        (if Nat.Coprime P.natAbs Q.natAbs then
          liftedResidueTest (residueTransform d) V outside h k (comparisonModulus h k outside n)
            (pairModulus_dvd_comparisonModulus h k outside n) (P,Q)*
          reindexedRealXi b s X tb td G h k hs ks (giantCoordinates h k) (pairBackground h k)
            (optionEquiv h k) (fun t=>match t with | none=>(P:ℝ) | some _=>(Q:ℝ)) else 0) := by
  rw [reindexedRealXi_option]
  simp only
  rw [realGiantSample_signed,realGiantSample_signed]
  unfold referenceTerm
  split_ifs <;> ring

theorem prime_referenceMean_eq_guarded (E : Finset ℕ) (hZ : 0<logCellMass G E) :
    primeMean (logCellPrimeSource G E hZ) (referenceTerm d V outside h k hs ks n b s X tb td G)=
      ((h.compensationProduct:ℂ)*(k.compensationProduct:ℂ))*
        guardedSourcePrimeMean (residueTransform d) V outside h k G E hZ
          (comparisonModulus h k outside n) (pairModulus_dvd_comparisonModulus h k outside n)
          (reindexedRealXi b s X tb td G h k hs ks (giantCoordinates h k) (pairBackground h k)
            (boolEquiv h k)) := by
  unfold primeMean
  simp_rw [referenceTerm_eq_bool,Int.natAbs_natCast,Int.cast_natCast,
    FinitePrior.cmean_mul_left]
  rfl

theorem mixed_referenceMean_eq_guarded (E : Finset ℕ) (hZ : 0<logCellMass G E) :
    mixedMean G (logCellPrimeSource G E hZ) (referenceTerm d V outside h k hs ks n b s X tb td G)=
      ((h.compensationProduct:ℂ)*(k.compensationProduct:ℂ))*
        guardedSourceMixedMean (residueTransform d) V outside h k G E hZ
          (comparisonModulus h k outside n) (pairModulus_dvd_comparisonModulus h k outside n)
          (reindexedRealXi b s X tb td G h k hs ks (giantCoordinates h k) (pairBackground h k)
            (optionEquiv h k)) := by
  unfold mixedMean
  simp_rw [referenceTerm_eq_option,Int.natAbs_natCast,Int.cast_natCast,
    FinitePrior.cmean_mul_left]
  unfold guardedSourceMixedMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have he : (fun q : (logCellPrimeSource G E hZ).Sample =>
      if p.Coprime q.val then
        liftedResidueTest (residueTransform d) V outside h k (comparisonModulus h k outside n)
          (pairModulus_dvd_comparisonModulus h k outside n) (p,q.val)*
        reindexedRealXi b s X tb td G h k hs ks (giantCoordinates h k) (pairBackground h k)
          (optionEquiv h k) (fun t=>match t with | none=>(p:ℝ) | some _=>(q.val:ℝ)) else 0)=
      (fun q => if p.Coprime q.val then
        liftedResidueTest (residueTransform d) V outside h k (comparisonModulus h k outside n)
          (pairModulus_dvd_comparisonModulus h k outside n) (p,q.val)*
        reindexedRealXi b s X tb td G h k hs ks (giantCoordinates h k) (pairBackground h k)
          (optionEquiv h k) (Option.elim' (p:ℝ) (fun _ : Unit=>(q.val:ℝ))) else 0) := by
    funext q
    split_ifs
    · congr 1
      apply congrArg (reindexedRealXi b s X tb td G h k hs ks
        (giantCoordinates h k) (pairBackground h k) (optionEquiv h k))
      funext i
      cases i <;> rfl
    · rfl
  rw [he]
  ring

end Ostmann.Arithmetic.HistoryGiantReferenceMean

end

end OAI
