import OAI.Computability.PerfectCompleteness.Decoding.LeftDecoder
import OAI.Computability.PerfectCompleteness.Foundations.TupleIndexEmitterLemmas

namespace OAI


namespace PerfectCompleteness.AffineDecoderMeeting

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

section Product

variable {L R : Type*} [Fintype L] [Fintype R]

theorem product_probability_lower
    (left : FiniteDistribution L) (right : FiniteDistribution R)
    (event : L × R → Bool) (good : R → Bool) (p : ℝ)
    (hpoint : ∀ y, good y = true →
      p ≤ left.probability (fun x => event (x, y))) :
    p * right.probability good ≤ (left.product right).probability event := by
  rw [UsefulAdvice.product_probability_advice_first]
  change p * (∑ y, if good y then right.weight y else 0) ≤
    ∑ y, right.weight y * left.probability (fun x => event (x, y))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  by_cases hy : good y = true
  · rw [ite_eq_left hy, mul_comm p]
    exact mul_le_mul_of_nonneg_left (hpoint y hy) (right.nonnegative y)
  · rw [ite_eq_right hy, mul_zero]
    exact mul_nonneg (right.nonnegative y) (left.probability_nonnegative _)

end Product

section Algebra

variable {H H' : Type*} [AddCommGroup H] [Module F2 H]
  [AddCommGroup H'] [Module F2 H']
  (i : H' →ₗ[F2] H) (B : Submodule F2 H)
  (C : Submodule F2 (Module.Dual F2 (H ⧸ B)))
  (center : Module.Dual F2 H)

def nativeQ : Submodule F2 (Module.Dual F2 H') :=
  (PulledColumnSpace.pulled B C).map i.dualMap

def nativeCenter : Module.Dual F2 H' := i.dualMap center

theorem candidate_mem_nativeCoset (q : PulledColumnSpace.Candidates B C center) :
    i.dualMap q.val - nativeCenter i center ∈ nativeQ i B C := by
  change i.dualMap q.val - i.dualMap center ∈
    (PulledColumnSpace.pulled B C).map i.dualMap
  rw [← map_sub]
  exact Submodule.mem_map_of_mem q.property

theorem exists_candidate_of_mem_nativeCoset (decoded : Module.Dual F2 H')
    (hdecoded : decoded - nativeCenter i center ∈ nativeQ i B C) :
    ∃ q : PulledColumnSpace.Candidates B C center, i.dualMap q.val = decoded := by
  obtain ⟨q, hq, heq⟩ := Submodule.mem_map.mp hdecoded
  refine ⟨PulledColumnSpace.candidateEquiv B C center ⟨q, hq⟩, ?_⟩
  change i.dualMap (center + q) = decoded
  rw [map_add, heq]
  change i.dualMap center + (decoded - i.dualMap center) = decoded
  abel

theorem nativeCoset_iff_exists_candidate (decoded : Module.Dual F2 H') :
    decoded - nativeCenter i center ∈ nativeQ i B C ↔
      ∃ q : PulledColumnSpace.Candidates B C center, i.dualMap q.val = decoded := by
  constructor
  · exact exists_candidate_of_mem_nativeCoset i B C center decoded
  · rintro ⟨q, rfl⟩
    exact candidate_mem_nativeCoset i B C center q

theorem finrank_nativeQ_le [FiniteDimensional F2 H] :
    Module.finrank F2 (nativeQ i B C) ≤ Module.finrank F2 C := by
  calc
    Module.finrank F2 (nativeQ i B C) ≤
        Module.finrank F2 (PulledColumnSpace.pulled B C) :=
      Submodule.finrank_map_le i.dualMap (PulledColumnSpace.pulled B C)
    _ = Module.finrank F2 C := PulledColumnSpace.finrank_pulled B C

end Algebra


variable {H H' : Type*} [AddCommGroup H] [Module F2 H]
  [AddCommGroup H'] [Module F2 H']
  [FiniteDimensional F2 H] [FiniteDimensional F2 H']

local instance leftDualFintype : Fintype (Module.Dual F2 H) :=
  LeftDecoder.dualFintype (V := H)

local instance nativeDualFintype : Fintype (Module.Dual F2 H') :=
  LeftDecoder.dualFintype (V := H')

variable (i : H' →ₗ[F2] H) (B : Submodule F2 H)
  (C : Submodule F2 (Module.Dual F2 (H ⧸ B)))
  (center : Module.Dual F2 H)

omit [FiniteDimensional F2 H'] in
theorem native_point_probability_lower {r : Nat}
    (hC : Module.finrank F2 C ≤ r) (decoded : Module.Dual F2 H')
    (hdecoded : decoded - nativeCenter i center ∈ nativeQ i B C) :
    1 / (2 : ℝ) ^ r ≤ (LeftDecoder.affineLaw B C center).probability
      (fun q => decide (i.dualMap q = decoded)) := by
  apply LeftDecoder.affineLaw_success_lower B C center hC
  obtain ⟨q, hq⟩ := exists_candidate_of_mem_nativeCoset i B C center decoded hdecoded
  exact ⟨q, decide_eq_true hq⟩

theorem meeting_probability_lower {r : Nat}
    (hC : Module.finrank F2 C ≤ r)
    (right : FiniteDistribution (Module.Dual F2 H')) :
    (1 / (2 : ℝ) ^ r) * right.probability
      (fun decoded => decide (decoded - nativeCenter i center ∈ nativeQ i B C)) ≤
      ((LeftDecoder.affineLaw B C center).product right).probability
        (fun pair => decide (i.dualMap pair.1 = pair.2)) := by
  apply product_probability_lower
  intro decoded hdecoded
  exact native_point_probability_lower i B C center hC decoded (of_decide_eq_true hdecoded)


end
end PerfectCompleteness.AffineDecoderMeeting

end OAI
