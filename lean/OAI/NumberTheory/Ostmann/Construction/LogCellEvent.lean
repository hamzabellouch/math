import OAI.NumberTheory.Ostmann.Construction.HarmonicPriorEvent
import OAI.NumberTheory.Ostmann.Construction.LogCellPrior

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open scoped BigOperators

theorem logCellPrior_event_mean (c : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass c E)
    (B : ℕ → Prop) [DecidablePred B] :
    (logCellPrior c E hZ).mean (fun p => if B (p:ℕ) then 1 else 0)=
      (∑p∈(logCellPrimes c\E).filter B,logCellWeight c p)/logCellMass c E := by
  change (∑p:LogCellSample c E,logCellWeight c p/
    (∑q:LogCellSample c E,logCellWeight c q)*(if B (p:ℕ) then 1 else 0))=_
  rw [logCell_sample_sum]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  have h := Finset.sum_coe_sort (logCellPrimes c\E)
    (fun p : ℕ => if B p then logCellWeight c p else 0)
  simpa only [Finset.sum_filter,mul_ite,mul_one,mul_zero] using h

end Ostmann.Construction

end

end OAI
