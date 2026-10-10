import OAI.Combinatorics.BalancedRyser.Candidates.CandidateOldExternalOverlap
import OAI.Combinatorics.BalancedRyser.Construction.ExternalWitnessPartition

namespace OAI

namespace Balanced.ExternalAssembly

noncomputable section
open scoped Classical BigOperators
open MeasureTheory CandidateExposure CandidateValidityWitness PartialAlignment
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance : MeasurableSpace F := ⊤

theorem oldOld_overlap_card_le (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) :
    ((witnesses g M).filter (fun w => w.2.1 ∈ D ∧ w.2.2 ∈ D ∧
      0 < (exposedTupleIndices w.1.1 D).card)).card ≤
      (CandidateOldExternal.oldOverlapWitnesses g D M).card := by
  rw [← CandidateOldExternal.keyWitnesses_card]
  apply Finset.card_le_card
  intro w hw
  rcases w with ⟨⟨T, i, j⟩, d, e⟩
  obtain ⟨hw, hdD, heD, hover⟩ := Finset.mem_filter.mp hw
  obtain ⟨hs, hij, hde, hd, he, hdT, heT, x, hx, hex, hdi, hej⟩ :=
    (mem_witnesses g M _).mp hw
  have hT : T ∈ eligibleTuples g :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.1, hs.2.1⟩
  have hsucc : M ∈ successfulInDirection T g :=
    ⟨⟨lineEval g (tuplePoint M T 0), hs.2.2.2⟩, hs.2.2.1⟩
  apply Finset.mem_filter.mpr
  constructor
  · simp only [CandidateOldExternal.oldOverlapPrescriptions, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_filter, Finset.mem_univ, and_true]
    exact ⟨⟨hT, hover⟩, hdD, heD⟩
  · exact ⟨hsucc, x, hx, hex, hij, hde, hd, he, hdT, heT, hdi, hej⟩

theorem oldOld_overlap_integral_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (∫ M, (((witnesses g M).filter (fun w => w.2.1 ∈ D ∧ w.2.2 ∈ D ∧
      0 < (exposedTupleIndices w.1.1 D).card)).card : ℝ)
        ∂(exposedLaw D a).toMeasure) ≤ 262144 * (m : ℝ)^2 * ((m : ℝ) + 1)^4 := by
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  apply le_trans _ (CandidateOldExternal.expected_oldOverlapWitnesses_le g D a m hD)
  apply Finset.sum_le_sum
  intro M hM
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  exact_mod_cast oldOld_overlap_card_le g D M

end
end Balanced.ExternalAssembly

end OAI
