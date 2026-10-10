import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReplacementErrorSelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralFiniteBounds

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkIntegralReplacement
open Construction HistoryBulkPriorGrid HistoryPrincipalIntegralAverage HistoryPrincipalIntegralFinite
open PrimeCellFreezing
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem sourceBulkMean_primeIntegral
    (L : ℝ) (E : Finset ℕ) (hZ : 0 < harmonicPrimeMass (bulkPrimeBand L E))
    (M : ℕ) [NeZero M] (hsize : (M:ℝ)<Real.exp (bulkLogLower L))
    (F : (ι → (ZMod M)ˣ) → ℂ) (lo hi Z : κ → ℝ) (hlo : ∀i,0<lo i)
    (f : (κ → ℝ) → (ι → ℝ) → ℂ)
    (hf : ∀p : ι → (bulkPrimeSource L E hZ).Sample,
      ContinuousOn (fun t => f (fun i=>Real.exp (t i)) (fun i=>((p i).val:ℝ)))
        (logRectangle lo hi)) :
    sourceBulkMean L E hZ M hsize F (fun x=>primeIntegral lo hi Z (fun y=>f y x)) =
      primeIntegral lo hi Z (fun y=>sourceBulkMean L E hZ M hsize F (f y)) := by
  classical
  unfold sourceBulkMean
  rw [primeIntegral_cmean (bulkProductPrior (ι:=ι) L E hZ) lo hi Z hlo
    (fun p y => F (fun i=>bulkPrimeUnit L M hsize (p i).val
      (bulkPrimeBand_subset_closed L E (p i).property))*f y (fun i=>((p i).val:ℝ)))
    (fun p=>continuousOn_const.mul (hf p))]
  unfold FinitePrior.cmean
  apply Finset.sum_congr rfl
  intro p hp
  dsimp only
  rw [primeIntegral_const_mul]

theorem sourceBulkMean_mixedIntegral
    (L : ℝ) (E : Finset ℕ) (hZ : 0 < harmonicPrimeMass (bulkPrimeBand L E))
    (M : ℕ) [NeZero M] (hsize : (M:ℝ)<Real.exp (bulkLogLower L))
    (F : (ι → (ZMod M)ˣ) → ℂ) (loI hiI G : ℝ) (φ : ℝ→ℝ)
    (lo hi Z : κ → ℝ) (hφ : Continuous φ) (hlo : ∀i,0<lo i)
    (f : (Option κ → ℝ) → (ι → ℝ) → ℂ)
    (hf : ∀p : ι → (bulkPrimeSource L E hZ).Sample,
      ContinuousOn (fun t => f (fun i=>Real.exp (t i)) (fun i=>((p i).val:ℝ)))
        (logRectangle (Option.elim' loI lo) (Option.elim' hiI hi))) :
    sourceBulkMean L E hZ M hsize F
        (fun x=>mixedIntegral loI hiI G φ lo hi Z (fun y=>f y x)) =
      mixedIntegral loI hiI G φ lo hi Z (fun y=>sourceBulkMean L E hZ M hsize F (f y)) := by
  classical
  unfold sourceBulkMean
  rw [mixedIntegral_cmean (bulkProductPrior (ι:=ι) L E hZ) loI hiI G φ lo hi Z hφ hlo
    (fun p y => F (fun i=>bulkPrimeUnit L M hsize (p i).val
      (bulkPrimeBand_subset_closed L E (p i).property))*f y (fun i=>((p i).val:ℝ)))
    (fun p=>continuousOn_const.mul (hf p))]
  unfold FinitePrior.cmean
  apply Finset.sum_congr rfl
  intro p hp
  dsimp only
  rw [mixedIntegral_const_mul]

omit [Fintype κ] [DecidableEq κ] in

theorem sourceBulkMean_continuousOn
    (L : ℝ) (E : Finset ℕ) (hZ : 0 < harmonicPrimeMass (bulkPrimeBand L E))
    (M : ℕ) [NeZero M] (hsize : (M:ℝ)<Real.exp (bulkLogLower L))
    (F : (ι → (ZMod M)ˣ) → ℂ) (S : Set (κ→ℝ))
    (f : (κ → ℝ) → (ι → ℝ) → ℂ)
    (hf : ∀p : ι → (bulkPrimeSource L E hZ).Sample,
      ContinuousOn (fun t => f (fun i=>Real.exp (t i)) (fun i=>((p i).val:ℝ))) S) :
    ContinuousOn (fun t=>sourceBulkMean L E hZ M hsize F (f (fun i=>Real.exp (t i)))) S := by
  classical
  unfold sourceBulkMean FinitePrior.cmean
  exact continuousOn_finsetSum _ (fun p _=>continuousOn_const.mul
    (continuousOn_const.mul (hf p)))

end Ostmann.Arithmetic.HistoryBulkIntegralReplacement

end

end OAI
