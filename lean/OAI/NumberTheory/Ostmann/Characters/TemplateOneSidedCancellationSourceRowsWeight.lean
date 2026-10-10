import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSourceRows

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators SchwartzMap FourierTransform
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateSupportRemoval Arithmetic HigherBiasSource.SourceTemplate
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [DecidableEq ι]

theorem canonicalSourceRowData_weight (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (j : ℕ) (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (i : ι) (x : Other i → ℤ)
    (Q : ℕ) (r n : ℤ)
    (hf : historyFrequencyBounds V j s t)
    (he : ∀ a u,HistoryReconstruction.Good a (e u))
    (hQ : residueModulus (historyResidueGuards k j s e t) ∣ (Q:ℤ))
    {X Δ W H : ℝ} (hX : 1 ≤ X) (hH : Real.log 2 ≤ H) (D : ℕ)
    (hs : ∀ u : Fin (2^j),(periodExpression k (indexedBottomExpressions k j b s e t u).2.2).syntaxSize ≤ D)
    (hfixed : ∀ u : Fin (2^j),(periodExpression k (indexedBottomExpressions k j b s e t u).2.2).FixedLogBound H)
    (hvars : ∀u,|((insertCoordinate i x ((Q:ℤ)*n+r) u : ℤ) : ℝ)| ≤ Real.exp H) :
    (canonicalSourceRowData k B V T J j b s e t i x r X Δ W H D).weight
      (𝓕 SchwartzCutoff.psi) (((Q:ℤ)*n+r):ℝ) =
      conjugateBy b (coreHistoryWeight k (fun l _ => B l) (fun l _ => V l)
        (canonicalHistoryExtra k (fun l => pivotWindow (T l) W))
        (canonicalHistoryMask k (sourceRangeLeafMask k J X Δ W))
        X Δ W j s (evalExpressions (insertCoordinate i x ((Q:ℤ)*n+r)) e) t) := by
  have hinv := frequencyArithmetic_progression_of_dvd k V j s e t hf he Q hQ i x r n
  unfold canonicalSourceRowData
  rw [gatedData_weight]
  by_cases hbase : frequencyArithmetic k V j s (evalExpressions (insertCoordinate i x r) e) t
  · simp only [hbase,decide_true,ite_true]
    simpa only [Int.cast_add,Int.cast_mul] using
      (canonicalSourceLeafData_weight k B V T J j b s e t i x _
        (Δ:=Δ) (W:=W) hX hH D (he _) hs hfixed hvars (hinv.mpr hbase))
  · have hactual : ¬frequencyArithmetic k V j s
        (evalExpressions (insertCoordinate i x ((Q:ℤ)*n+r)) e) t :=
      fun h => hbase (hinv.mp h)
    simp only [hbase,decide_false,Bool.false_eq_true,ite_false]
    rw [canonicalSourceCoreWeight_eq_profiles k B V T J X Δ W
      (lt_of_lt_of_le (by norm_num) hX) j b s e t _]
    simp only [hactual,false_and,ite_false]

theorem canonicalSourceRowData_weight_nat (k : ℕ) (B V : ℕ → ℤ) (T : ℕ → ℝ)
    (J : ℤ) (j : ℕ) (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (i : ι) (x : Other i → ℤ)
    (Q r n : ℕ)
    (hf : historyFrequencyBounds V j s t)
    (he : ∀ a u,HistoryReconstruction.Good a (e u))
    (hQ : residueModulus (historyResidueGuards k j s e t) ∣ (Q:ℤ))
    {X Δ W H : ℝ} (hX : 1 ≤ X) (hH : Real.log 2 ≤ H) (D : ℕ)
    (hs : ∀ u : Fin (2^j),(periodExpression k (indexedBottomExpressions k j b s e t u).2.2).syntaxSize ≤ D)
    (hfixed : ∀ u : Fin (2^j),(periodExpression k (indexedBottomExpressions k j b s e t u).2.2).FixedLogBound H)
    (hvars : ∀u,|((insertCoordinate i x ((Q*n+r:ℕ):ℤ) u : ℤ) : ℝ)| ≤ Real.exp H) :
    (canonicalSourceRowData k B V T J j b s e t i x (r:ℤ) X Δ W H D).weight
      (𝓕 SchwartzCutoff.psi) ((Q*n+r:ℕ):ℝ) =
      conjugateBy b (coreHistoryWeight k (fun l _ => B l) (fun l _ => V l)
        (canonicalHistoryExtra k (fun l => pivotWindow (T l) W))
        (canonicalHistoryMask k (sourceRangeLeafMask k J X Δ W))
        X Δ W j s (evalExpressions (insertCoordinate i x ((Q*n+r:ℕ):ℤ)) e) t) := by
  have hv : ∀u,|((insertCoordinate i x ((Q:ℤ)*(n:ℤ)+(r:ℤ)) u : ℤ) : ℝ)| ≤ Real.exp H := by
    simpa only [Nat.cast_add,Nat.cast_mul] using hvars
  simpa only [Nat.cast_add,Nat.cast_mul,Int.cast_add,Int.cast_mul,Int.cast_natCast] using
    canonicalSourceRowData_weight k B V T J j b s e t i x Q (r:ℤ) (n:ℤ)
      hf he hQ hX hH D hs hfixed hv

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
