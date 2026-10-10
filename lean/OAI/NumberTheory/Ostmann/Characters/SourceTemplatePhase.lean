import OAI.NumberTheory.Ostmann.Characters.SourceTemplatePhaseCore
import OAI.NumberTheory.Ostmann.Characters.SourceTemplateState

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template
open scoped BigOperators ComplexConjugate FourierTransform
attribute [local instance] Classical.propDecidable

theorem sourceSample_unitHistoryPhase {k Q:ℕ} (cfg:SourceConfiguration k) (m:ℕ)
    (χ:Fin (sourceHalfSize cfg m)→(q:ℕ)→MulChar (ZMod q) ℂ)
    (a:Fin (sourceHalfSize cfg m)→(q:ℕ)→ZMod q)
    (ζ:Fin (sourceHalfSize cfg m)→ℕ→ℂ)
    (w:Fin (sourceHalfSize cfg m+sourceHalfSize cfg m)→PrimeUpTo Q)
    (s:ℤ) (t:HistoryReconstruction.Tree 0) :
    unitHistoryPhase k 0 (sourceWidth cfg m)
      (sourceUnitData cfg m ζ) (sourceCharacterData cfg m χ) (sourceTranslationData cfg m a)
      (sourceSample cfg m w) s t =
      letI : ∀i,Fact (w i).val.Prime := fun i => ⟨primeUpTo_prime (w i)⟩
      (∏i,characterDoublePhase ζ i (w i).val)*
        initialPhase (fun i => (w i).val) (fun i => characterDoubleChar χ i (w i).val)
          (fun i => characterDoubleCenter a i (w i).val) s :=
  sourcePullback_unitHistoryPhase cfg m χ a ζ w s t

theorem characterTupleFourier_eq_source_sum {k Q:ℕ} (cfg:SourceConfiguration k) (m:ℕ)
    (χ:Fin (sourceHalfSize cfg m)→(q:ℕ)→MulChar (ZMod q) ℂ)
    (a:Fin (sourceHalfSize cfg m)→(q:ℕ)→ZMod q)
    (ζ:Fin (sourceHalfSize cfg m)→ℕ→ℂ) (X:ℝ)
    (w:Fin (sourceHalfSize cfg m+sourceHalfSize cfg m)→PrimeUpTo Q) :
    characterTupleFourier (characterDoubleChar χ) (characterDoubleCenter a)
      (characterDoublePhase ζ) X w =
    ∑' s:ℤ,
      (Real.sqrt (X/(period k 0 (constituentSampleState (schedule k 0) (sourceWidth cfg m)
        (sourceSample cfg m w)):ℝ)):ℂ)*
      𝓕 SchwartzCutoff.psi (-(s:ℝ)*X/(period k 0
        (constituentSampleState (schedule k 0) (sourceWidth cfg m) (sourceSample cfg m w)):ℝ))*
      unitHistoryPhase k 0 (sourceWidth cfg m)
        (sourceUnitData cfg m ζ) (sourceCharacterData cfg m χ) (sourceTranslationData cfg m a)
        (sourceSample cfg m w) s PUnit.unit := by
  let : ∀i,Fact (w i).val.Prime := fun i => ⟨primeUpTo_prime (w i)⟩
  simp_rw [sourceSample_period cfg m w,Int.cast_natCast,sourceSample_unitHistoryPhase cfg m χ a ζ w]
  unfold characterTupleFourier
  have he (s:ℤ) :
      (Real.sqrt (X/(characterTupleProduct w:ℝ)):ℂ)*
        𝓕 SchwartzCutoff.psi (-(s:ℝ)*X/(characterTupleProduct w:ℝ))*
        ((∏i,characterDoublePhase ζ i (w i).val)*
          initialPhase (fun i => (w i).val) (fun i => characterDoubleChar χ i (w i).val)
            (fun i => characterDoubleCenter a i (w i).val) s) =
      ((∏i,characterDoublePhase ζ i (w i).val)*(Real.sqrt (X/(characterTupleProduct w:ℝ)):ℂ))*
        (initialPhase (fun i => (w i).val) (fun i => characterDoubleChar χ i (w i).val)
          (fun i => characterDoubleCenter a i (w i).val) s *
          𝓕 SchwartzCutoff.psi (-(s:ℝ)*X/(characterTupleProduct w:ℝ))) := by ring
  simp_rw [he]
  rw [tsum_mul_left]

theorem characterTupleFourier_eq_leaf_sum {k Q:ℕ} (cfg:SourceConfiguration k) (m:ℕ)
    (χ:Fin (sourceHalfSize cfg m)→(q:ℕ)→MulChar (ZMod q) ℂ)
    (a:Fin (sourceHalfSize cfg m)→(q:ℕ)→ZMod q)
    (ζ:Fin (sourceHalfSize cfg m)→ℕ→ℂ) (X Δ W:ℝ)
    (w:Fin (sourceHalfSize cfg m+sourceHalfSize cfg m)→PrimeUpTo Q)
    (hlog:Real.log X+Δ-W≤Real.log (characterTupleProduct w:ℝ)) :
    characterTupleFourier (characterDoubleChar χ) (characterDoubleCenter a)
      (characterDoublePhase ζ) X w =
    ∑' s:ℤ, leafWeight k X Δ W s
      (constituentSampleState (schedule k 0) (sourceWidth cfg m) (sourceSample cfg m w))*
      unitHistoryPhase k 0 (sourceWidth cfg m)
        (sourceUnitData cfg m ζ) (sourceCharacterData cfg m χ) (sourceTranslationData cfg m a)
        (sourceSample cfg m w) s PUnit.unit := by
  rw [characterTupleFourier_eq_source_sum cfg m χ a ζ X w]
  apply tsum_congr
  intro s
  have hp:(0:ℝ)<characterTupleProduct w:=by exact_mod_cast characterTupleProduct_pos w
  simp only [leafWeight,sourceSample_period cfg m w,Int.cast_natCast,hp,hlog,and_self,ite_true]

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
