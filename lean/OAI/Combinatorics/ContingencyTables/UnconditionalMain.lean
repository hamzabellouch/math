import OAI.Combinatorics.ContingencyTables.Sampling.AllSamplingMachine
import OAI.Combinatorics.ContingencyTables.Sampling.ExactSamplingMachine
import OAI.Combinatorics.ContingencyTables.Counting.CountingMainMachine
import OAI.Combinatorics.ContingencyTables.Dense.FiniteBoxPrekopa
import OAI.Combinatorics.ContingencyTables.Dense.FiniteCheegerProof
import OAI.Combinatorics.ContingencyTables.Transport.EdmondsKarpBound

namespace OAI

/-! # Sampling and counting contingency tables with arbitrary margins

The finite-box Prékopa–Leindler inequality, finite Cheeger inequality
and Edmonds–Karp bound yield sampling and counting algorithms with
uniform polynomial bit-cost guarantees.
-/
namespace ContingencyTables

/-- Paper 200-01: an almost-uniform sampler with polynomial cost on every execution. -/
theorem boundedSampling : Algorithms.BoundedSamplingStatement :=
  SmallGraphProfiles.boundedSampling_conditional
    PublishedInputs.finiteBoxPrekopaLeindler (fun _ _ => CheegerProof.finiteCheeger)

/-- Paper 200-01: exact uniform sampling in expected polynomial bit time. -/
theorem exactSampling : Algorithms.ExactSamplingStatement :=
  SmallGraphProfiles.exactSampling_conditional
    PublishedInputs.finiteBoxPrekopaLeindler (fun _ _ => CheegerProof.finiteCheeger)

/-- Paper 200-02: the cell-bounded counting FPRAS with a public fair-bit machine. -/
theorem counting : Algorithms.CountingStatement :=
  CountingExecutedMachine.counting_conditional EdmondsKarpBound.edmondsKarp1972Theorem1
    PublishedInputs.finiteBoxPrekopaLeindler (fun _ _ => CheegerProof.finiteCheeger)

end ContingencyTables

end OAI
