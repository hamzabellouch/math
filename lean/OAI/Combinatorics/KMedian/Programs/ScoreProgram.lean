import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryAutoExtras
import OAI.Combinatorics.KMedian.Programs.FinsetMaskProgram
import OAI.Combinatorics.KMedian.Geometry.RationalCompletedCost

namespace OAI


                                    
section
namespace MetricKMedian.Completion.Rational.ScoreProgram
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row setView)
def raw (x : List (List ℚ) × Row) : ℚ :=
  (x.1.map (fun d => LPBinary.minimum (MaskProgram.selectedValues (d,x.2)))).sum
@[fun_prop] theorem raw_poly : Poly raw := by
  have hm : Poly LPBinary.minimum := ⟨LPBinary.Program.minimumProgram⟩
  unfold raw
  apply comp rat_sum
  apply list_map <;> fun_prop
 theorem raw_score {j f : ℕ} (d : Fin j → Fin f → ℚ) (O : Finset (Fin f)) :
    raw (List.ofFn (fun c => List.ofFn (d c)),setView O)=score d O := by
  unfold raw score
  rw [List.map_ofFn,List.sum_ofFn]
  apply sum_congr rfl
  intro c _
  dsimp only [Function.comp_def]
  by_cases h : O.Nonempty
  · rw [dite_eq_left h]
    exact LPBinary.minimum_eq_finset _ _ (h.image _) (MaskProgram.selectedValues_mem (d c) O)
  · rw [dite_eq_right h]
    have he : MaskProgram.selectedValues (List.ofFn (d c),setView O)=[] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro q hq
      obtain ⟨i,hi,_⟩ := mem_image.mp ((MaskProgram.selectedValues_mem (d c) O q).mp hq)
      exact h ⟨i,hi⟩
    rw [he]
    rfl
end MetricKMedian.Completion.Rational.ScoreProgram
end

end OAI
