import Mathlib
import OAI.Analysis.Commutator.OperatorAmplification

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace Topology

open ContinuousLinearMapWOT

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

omit [CompleteSpace H] in
lemma norm_single_eq (i : ι) (x : H) : ‖single ι i x‖=‖x‖ := by
  have he : single ι i x=PiLp.single 2 i x := by
    ext j
    simp [PiLp.single_apply]
  rw [he,PiLp.norm_single]

omit [CompleteSpace H] in
lemma norm_entry_le (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) (i j : ι) :
    ‖entry ι T i j‖≤‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (entry ι T i j) (norm_nonneg T)
  intro x
  change ‖T (single ι j x) i‖≤‖T‖*‖x‖
  calc
    _ ≤ ‖T (single ι j x)‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖T‖*‖single ι j x‖ := T.le_opNorm _
    _ = ‖T‖*‖x‖ := by rw [norm_single_eq]

omit [CompleteSpace H] in
lemma continuous_entryWOT (i j : ι) :
    Continuous (fun T : SumSpace (H:=H) ι →WOT[ℂ] SumSpace (H:=H) ι =>
      ofCLM (entry ι T.toCLM i j)) := by
  change Continuous (fun T : SumSpace (H:=H) ι →WOT[ℂ] SumSpace (H:=H) ι =>
    (ofCLM (PiLp.proj 2 (fun _ : ι => H) i)).comp ((T).comp (ofCLM (single ι j))))
  exact (continuous_postcomp _).comp (continuous_precomp _)

end Kadison.OperatorAmplification

end

end
end

end OAI
