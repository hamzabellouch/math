import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualCorrectedPrincipalBlockFamilyDensityBound
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualCorrectedPrincipalBlockFamilyDensityStatement
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualCorrectedPrincipalBlockFamilySelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatchedDensityRoot

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualCorrectedPrincipalBlockFamily
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkIndependentFibreReference
open HistoryBulkActualPrincipalBlockFamily HistoryBulkActualGoodPrincipal
open HistoryBulkPrincipalKernelReplacementMatched Filter
attribute [local instance] Classical.propDecidable

theorem selected_corrected_principal_factory_density_kernel_error_eventually
    (d : Decomposition) (Bs BD Bz D H : ℝ) {k : ℕ}
    (hBs : 0≤Bs)(hH : 0≤H)(hk : 0<k) :
    SelectedCorrectedDensityKernelEstimate d Bs BD Bz D H k := by
  exact ((selected_corrected_principal_factory_kernel_error_eventually d Bs BD Bz D H hBs hH hk).and
    (selected_root_density_principal_kernel_error_eventually d Bs BD Bz D H hBs hH hk)).mono
    (fun L h E C hG hGu hcl hcu hb hd spectator hspec outside houtside n hlen hsize l hl e he =>
      (h.1 E C hG hGu hcl hcu hb hd spectator hspec outside houtside n hlen hsize l hl e he).elim
        (fun hprime hex => hex.elim (fun hV _ =>
          ⟨hprime,hV,fun mask =>
            @correctedDensityKernelError_bound d Bs BD Bz L k l E C outside e he n hlen hprime hV
              (Real.exp (D*(L+1)^2))
              (Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)))
              (Real.exp (-H*(bulkSize k L:ℝ)))
              (h.2 E C hG hGu hcl hcu hb hd spectator hspec l true true hl
                outside (fun q hq=>(hprime q hq).pos) hsize
                (fun q hq=>(houtside q hq).elim (fun r hr=>hr ▸ (hspec r).2))) mask⟩)))

end Ostmann.Arithmetic.HistoryBulkActualCorrectedPrincipalBlockFamily

end

end OAI
