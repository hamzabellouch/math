import Mathlib
import OAI.Analysis.Commutator.MatrixEntryWOT

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

def position (i j : ι) (a : H →L[ℂ] H) : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι :=
  (single ι i).comp (a.comp (PiLp.proj 2 (fun _ : ι => H) j))

omit [CompleteSpace H] [Fintype ι] in
@[simp] lemma position_apply (i j : ι) (a : H →L[ℂ] H) (v : SumSpace (H:=H) ι) :
    position ι i j a v=single ι i (a (v j)) := rfl

omit [CompleteSpace H] in
lemma norm_position_le (i j : ι) (a : H →L[ℂ] H) : ‖position ι i j a‖≤‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
  intro v
  rw [position_apply,norm_single_eq]
  exact (a.le_opNorm _).trans (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v j) (norm_nonneg a))

omit [CompleteSpace H] [Fintype ι] in
lemma entry_position (i j : ι) (a : H →L[ℂ] H) :
    entry ι (position ι i j a) i j=a := by
  ext x
  simp

omit [CompleteSpace H] in
lemma norm_position (i j : ι) (a : H →L[ℂ] H) : ‖position ι i j a‖=‖a‖ := by
  apply le_antisymm (norm_position_le ι i j a)
  simpa only [entry_position] using norm_entry_le ι (position ι i j a) i j

lemma diagonal_commutator_position (T a : H →L[ℂ] H) (i j : ι) :
    diagonal (H:=H) ι T*position ι i j a-position ι i j a*diagonal (H:=H) ι T=
      position ι i j (T*a-a*T) := by
  ext v k
  simp only [sub_apply,mul_apply_eq_comp,position_apply,diagonal_single,
    diagonal_apply]
  simp only [single_apply]
  by_cases h : k=i <;> simp [h]

lemma norm_diagonal_commutator_position (T a : H →L[ℂ] H) (i j : ι) :
    ‖diagonal (H:=H) ι T*position ι i j a-position ι i j a*diagonal (H:=H) ι T‖=‖T*a-a*T‖ := by
  rw [diagonal_commutator_position,norm_position]

end Kadison.OperatorAmplification

end

end
end

end OAI
