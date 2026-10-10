import OAI.NumberTheory.Ostmann.Arithmetic.HistoryActualComparisonDecayArithmetic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open HistoryActualComparisonDecayArithmetic

theorem five_stage_bounds_of_eq {F H m : ℝ} (hm : 1 ≤ m)
    (a b b' c c' d e f : ℂ) (hb : b = b') (hc : c = c')
    (h0 : ‖a-b‖ ≤ Real.exp (-F-(H+5)*m) ∧ ‖a-b‖ ≤ Real.exp (-(H+5)*m))
    (h1 : ‖b'-c‖ ≤ Real.exp (-F-(H+5)*m) ∧ ‖b'-c‖ ≤ Real.exp (-(H+5)*m))
    (h2 : ‖c'-d‖ ≤ Real.exp (-F-(H+5)*m) ∧ ‖c'-d‖ ≤ Real.exp (-(H+5)*m))
    (h3 : ‖d-e‖ ≤ Real.exp (-F-(H+5)*m) ∧ ‖d-e‖ ≤ Real.exp (-(H+5)*m))
    (h4 : ‖e-f‖ ≤ Real.exp (-F-(H+5)*m) ∧ ‖e-f‖ ≤ Real.exp (-(H+5)*m)) :
    ‖a-f‖ ≤ Real.exp (-F-H*m) ∧ ‖a-f‖ ≤ Real.exp (-H*m) :=
  let hb' := congrArg (fun z : ℂ => ‖z-c‖) hb
  let hc' := congrArg (fun z : ℂ => ‖z-d‖) hc
  ⟨five_stage_exp_le hm a b c d e f h0.1 (hb'.trans_le h1.1)
      (hc'.trans_le h2.1) h3.1 h4.1,
    five_stage_bulk_exp_le hm a b c d e f h0.2 (hb'.trans_le h1.2)
      (hc'.trans_le h2.2) h3.2 h4.2⟩

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
