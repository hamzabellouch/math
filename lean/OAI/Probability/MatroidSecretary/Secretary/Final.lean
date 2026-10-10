import OAI.Probability.MatroidSecretary.Secretary.SourceAssembly
import OAI.Probability.MatroidSecretary.Secretary.Coupling

namespace OAI

/-!
# The full-seed order-oblivious secretary consequence

The concrete initial seed law is fixed before the weight vector.  The complete
conditional table is drawn initially and the decoder uses only prefix labels.
The actual rule's guarded replay is feasible at every seed, while the exact
source-law coupling supplies the expected-minimum guarantee against every
measurable full-information suffix policy.
-/

namespace MatroidProphet

/-- `cor:secretary`, with no construction-law or model-validity assumption. -/
theorem secretary.{u} : SecretaryChallenge.{u} := by
  intro n M hE
  exact SecretaryReplay.reconstructed_source_witness M hE
    (Secretary.couplingLength M hE) Secretary.couplingDecode
    (Secretary.couplingSeedLaw M hE)
    (Secretary.coupling_source_law M hE) (Secretary.coupling_mask_ae M hE)

end MatroidProphet

end OAI
