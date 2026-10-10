import OAI.Analysis.Laughlin.FourBody.SliceCoefficient
import OAI.Analysis.Laughlin.FourBody.WeightedReadout

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

noncomputable def limitFourCopyEnd (Q r D : ℕ) : Module.End ℂ (Space Q) :=
  ∑ p ∈ Finset.range (D+1), weightedFourEnd Q p (fun j k => limitSliceCoefficient r D p j.val k.val)

theorem limitFourCopyEnd_Slater_readout (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r)
    (a b c d : Fin (Q+1)) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hT : a.val+b.val+c.val+d.val=D+1) :
    limitFourCopyEnd Q r D (create a (create b (create c (create d (1 : Space Q))))) =
      (limitSlaterCoefficient D r a.val b.val c.val d.val : ℂ) • (1 : Space Q) := by
  simp only [limitFourCopyEnd,LinearMap.sum_apply]
  simp_rw [weightedFourEnd_readout Q _ _
    (fun j k => limitSliceCoefficient_antisymmetric r D _ j.val k.val hr hor)]
  rw [← Finset.sum_smul,← Complex.ofReal_sum]
  apply congrArg (fun v : ℝ => (v : ℂ) • (1 : Space Q))
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]
  rw [sum_pairLimit_slice D r a.val b.val c.val d.val hab hT,
    sum_pairLimit_slice D r a.val c.val b.val d.val (by exact_mod_cast lt_trans hab hbc) (by omega),
    sum_pairLimit_slice D r a.val d.val b.val c.val (by exact_mod_cast lt_trans hab (lt_trans hbc hcd)) (by omega),
    sum_pairLimit_slice D r b.val c.val a.val d.val hbc (by omega),
    sum_pairLimit_slice D r b.val d.val a.val c.val (by exact_mod_cast lt_trans hbc hcd) (by omega),
    sum_pairLimit_slice D r c.val d.val a.val b.val hcd (by omega)]
  rfl

theorem source_fourBody_physical_L (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r)
    (a b c d : Fin (Q+1)) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hT : a.val+b.val+c.val+d.val=D+1) :
    limitFourCopyEnd Q r D (create a (create b (create c (create d (1 : Space Q))))) =
      ((Real.sqrt (sourceCopyWeight D r /
        ((a.val.factorial : ℝ)*b.val.factorial*c.val.factorial*d.val.factorial)) *
        (Certificate.L D r (a.val,b.val,c.val,d.val) : ℝ) : ℝ) : ℂ) • (1 : Space Q) := by
  rw [limitFourCopyEnd_Slater_readout Q r D hr hor a b c d hab hbc hcd hT,
    source_fourBody_Slater_coefficient D r a.val b.val c.val d.val hr hor hab hbc hcd hT]

end Laughlin.Fock

end OAI
