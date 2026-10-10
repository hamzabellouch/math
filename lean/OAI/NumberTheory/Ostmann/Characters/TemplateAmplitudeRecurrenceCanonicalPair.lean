import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceCanonical
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceNodeSupport

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

theorem canonical_weight_pair_of_reversal (k j : ℕ) (hj:j<k)
    (B V : (j:ℕ) → State k (j+1) → ℤ) (R : ℕ → Finset ℕ+)
    (leafMask : ℤ → State k 0 → Prop) (X Δ W : ℝ)
    (hL hR : CopiedState k j) (y : OutsideState k j)
    (P : ℕ+) (s v w : ℤ) (tL tR : HistoryReconstruction.Tree j)
    (hl : CurrentAtomSupport k j v (sourceState k j (P:ℤ) hL y))
    (hr : CurrentAtomSupport k j w (sourceState k j (P:ℤ) hR y))
    (hn : CurrentAtomSupport k (j+1) s (pairedState k j hL hR y))
    (he : v*(∏i,hR i)-w*(∏i,hL i)=s*(P:ℤ)) (hP : P∈R j)
    (hPB : (P:ℤ)≤B j (pairedState k j hL hR y))
    (hv : |v|≤V j (pairedState k j hL hR y))
    (hw : |w|≤V j (pairedState k j hL hR y))
    (hgap : 2*B j (pairedState k j hL hR y)*V j (pairedState k j hL hR y)<∏i,hR i) :
    retainedHistoryWeight k B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
      X Δ W (j+1) s (pairedState k j hL hR y) ((v,w),tL,tR) =
      retainedHistoryWeight k B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
        X Δ W j v (sourceState k j (P:ℤ) hL y) tL *
      conj (retainedHistoryWeight k B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
        X Δ W j w (sourceState k j (P:ℤ) hR y) tR) := by
  obtain ⟨hnode,hint⟩ := nodeSupports_pairedState_of_reversal hj hl hr hn he hPB hv hw hgap
  have hrec := reconstructedPivot_pairedState_of_reversal (y:=y) hn.root_ne_zero he
  have hex : canonicalHistoryExtra k R (j+1) s (pairedState k j hL hR y) ((v,w),tL,tR) :=
    ⟨P,hP,hrec⟩
  rw [canonical_retainedHistoryWeight_succ k j B V R leafMask X Δ W s _ _ hn hnode hint,
    ite_eq_left hex]
  simp only [hrec,childState_pairedState,ite_true,Bool.false_eq_true,ite_false]

end Ostmann.Characters.Template

end

end OAI
