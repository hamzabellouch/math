import OAI.Combinatorics.BalancedRyser.Candidates.ExternalWitnessMoments
import OAI.Combinatorics.BalancedRyser.Candidates.ExternalWitnessTail
import OAI.Combinatorics.BalancedRyser.Incidence.CandidateIncidenceCompletion

namespace OAI

noncomputable section

namespace Balanced
open scoped _root_.Balanced

open Filter
open scoped Topology

universe u

namespace CandidateGraphEndpoint

def externalMomentConstant : ℝ :=
  (ExternalAssembly.exposureConstant (399 * 6)) ^ 400

theorem externalMomentConstant_pos : 0 < externalMomentConstant :=
  pow_pos (ExternalAssembly.exposureConstant_pos _) _

theorem tendsto_sizeGood
    (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | CandidateIncidenceTests.SizeGood M
        CandidateAbundanceAssembly.slotLinearConstant}) atTop (𝓝 1) := by
  have hslots := ExternalWitnessTail.candidateSlots_of_uniform_moment
    externalMomentConstant externalMomentConstant_pos.le F hq
    (fun n g => ExternalAssembly.witnesses_original_moment_le g 400)
  convert hslots using 1
  funext n
  congr 1
  ext M
  constructor
  · intro h s
    exact ⟨h s, candidateSlot_card_le M s⟩
  · intro h s
    exact (h s).1

end CandidateGraphEndpoint

theorem candidateGraph_proof : CandidateGraphResult.{u} :=
  CandidateIncidenceTests.candidateGraphResult_of_size_estimate
    CandidateAbundanceAssembly.slotLinearConstant
    CandidateAbundanceAssembly.slotLinearConstant_pos
    CandidateGraphEndpoint.tendsto_sizeGood

end Balanced

end

end OAI
