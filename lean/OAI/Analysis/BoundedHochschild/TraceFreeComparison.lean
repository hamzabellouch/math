import OAI.Analysis.BoundedHochschild.PartialIsometryChains
import OAI.Analysis.BoundedHochschild.TraceFreeSeparation
import OAI.Analysis.BoundedHochschild.CentralComparison

namespace OAI

/-!
# Projection comparison before constructing a trace

Maximal partial isometries and the central comparison theorem are constructed
directly from a predual. Their proofs do not presuppose the trace whose
existence is needed in the finite-algebra reduction.
-/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison FinitePathMain

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The unmatched remainders of a maximal partial isometry have no connecting corner. -/
theorem exists_maximal_partialIso (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ∃ v : PartialIso M, v.initial ≤ p ∧ v.final ≤ q ∧
      ∀ a : M, (q - v.final) * a * (p - v.initial) = 0 := by
  classical
  let S : Set (PartialIso M) := {v | v.initial ≤ p ∧ v.final ≤ q}
  have hz : (0 : PartialIso M) ∈ S :=
    ⟨by simpa using hp.nonneg, by simpa using hq.nonneg⟩
  obtain ⟨v, _, hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain y hy => by
    obtain ⟨s, hsp, hsq, hu⟩ := partialIso_chain_upper e hp hq c hchain ⟨y, hy⟩
      (fun z hz => hc hz)
    exact ⟨s, ⟨hsp, hsq⟩, hu⟩) 0 hz
  have hvp : v.initial ≤ p := hmax.1.1
  have hvq : v.final ≤ q := hmax.1.2
  refine ⟨v, hvp, hvq, fun a => ?_⟩
  by_contra ha
  have hp' := (v.initial_proj.le_iff_sub hp).mp hvp
  have hq' := (v.final_proj.le_iff_sub hq).mp hvq
  obtain ⟨w, hw0, hwp, hwq⟩ := partialIso_of_nonzero_corner e hq' hp'
    ((q - v.final) * a * (p - v.initial)) ha
    (by rw [← mul_assoc, ← mul_assoc, hq'.isIdempotentElem.eq])
    (by rw [mul_assoc, hp'.isIdempotentElem.eq])
  have hi := HochschildCentralComparison.orthogonal_of_le_sub
    hp v.initial_proj w.initial_proj hvp hwp
  have hf := HochschildCentralComparison.orthogonal_of_le_sub
    hq v.final_proj w.final_proj hvq hwq
  have hs : v.orthogonalSum w hi hf ∈ S := by
    constructor
    · rw [PartialIso.orthogonalSum_initial]
      calc
        v.initial + w.initial ≤ v.initial + (p - v.initial) := add_le_add_right hwp _
        _ = p := by abel
    · rw [PartialIso.orthogonalSum_final]
      calc
        v.final + w.final ≤ v.final + (q - v.final) := add_le_add_right hwq _
        _ = q := by abel
  have hle := v.le_orthogonalSum w hi hf
  have he := le_antisymm (hmax.2 hs hle) hle
  have hvw : (v : M) + w = v := congrArg (fun z : PartialIso M => (z : M)) he
  exact hw0 (add_eq_left.mp hvw)

/-- Murray--von Neumann comparison over complementary central parts, with no
trace assumption. This is the structural comparison used before trace existence. -/
theorem trace_free_central_comparison (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ∃ (z : M) (v : PartialIso M), CentralProjection z ∧ v.initial ≤ p ∧ v.final ≤ q ∧
      z * v.final = z * q ∧ (1 - z) * v.initial = (1 - z) * p := by
  obtain ⟨v, hvp, hvq, horth⟩ := exists_maximal_partialIso e hp hq
  have hp' := (v.initial_proj.le_iff_sub hp).mp hvp
  have hq' := (v.final_proj.le_iff_sub hq).mp hvq
  have horth' : ∀ a : M, (p - v.initial) * a * (q - v.final) = 0 := by
    intro a
    have h := congrArg star (horth (star a))
    simpa only [star_mul, star_star, star_zero, hp'.isSelfAdjoint.star_eq,
      hq'.isSelfAdjoint.star_eq, mul_assoc] using h
  obtain ⟨z, hz, hpz, hzq⟩ := exists_trace_free_central_separator e hp' hq' horth'
  have hzp : z * (p - v.initial) = p - v.initial :=
    (hp'.le_iff_mul_eq_right hz.1).mp hpz
  refine ⟨z, v, hz, hvp, hvq, ?_, ?_⟩
  · exact (sub_eq_zero.mp (by simpa only [mul_sub] using hzq)).symm
  · have h : (1 - z) * (p - v.initial) = 0 := by
      rw [sub_mul, one_mul, hzp, sub_self]
    exact (sub_eq_zero.mp (by simpa only [mul_sub] using h)).symm

end KadisonRingrose
end BoundedHochschild

end

end OAI
