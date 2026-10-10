import OAI.Combinatorics.BalancedRyser.Local.AlignedListProbability
import OAI.Combinatorics.BalancedRyser.Probability.EqualityPatternOrdering

namespace OAI

namespace Balanced.Local

open AlignedListProbability
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [Fintype F] in

theorem smallReuseOrder_prescribed {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (ha : Function.Injective a.2)
    (bits : Bits b) (l : List (Fin b)) (h : SmallReuseOrder P.classSet l) :
    SmallReuseOrder (fun i => generatorSet (prescribedTuple P a bits i)) l := by
  induction l with
  | nil => trivial
  | cons i l ih =>
      refine ⟨ih h.1, ?_⟩
      rw [P.prescribed_generator_overlap_card a ha bits i l.toFinset]
      exact h.2

theorem alignment_probability {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) :
    offsetProbability (Aligned P a bits p) =
      1 / (Fintype.card F : ℝ) ^ (4 * b) := by
  obtain ⟨l, hnd, hfull, horder⟩ := P.exists_smallReuseOrder hκ
  have hlen : l.length = b := by
    rw [← List.toFinset_card_of_nodup hnd, hfull]
    simp
  have hall (i : Fin b) : i ∈ l := by
    apply List.mem_toFinset.mp
    rw [hfull]
    exact Finset.mem_univ _
  have hgenerators (i : Fin b) : Function.Injective (prescribedTuple P a bits i).generator :=
    ha.2.1.comp (P.withinTuple i)
  have htargets (i : Fin b) (j : Fin 4) :
      (prescribedTuple P a bits i).generator j ≠ (lineThrough (a.1 i) p).1 :=
    ha.2.2 i j
  have hprob := list_alignment_probability (prescribedTuple P a bits)
    (fun i => lineThrough (a.1 i) p) l (fun i _ => hgenerators i)
    (fun i _ => htargets i) (smallReuseOrder_prescribed P a ha.2.1 bits l horder)
  have hevent :
      {M | ListAligned (prescribedTuple P a bits) (fun i => lineThrough (a.1 i) p) l M} =
        {M | Aligned P a bits p M} := by
    ext M
    constructor
    · intro h ij
      exact h ij.1 (hall ij.1) ij.2
    · intro h i _ j
      exact h (i,j)
  rw [hevent, hlen] at hprob
  calc
    offsetProbability (Aligned P a bits p) =
        ((PMF.uniformOfFintype (MergedPairs F)).toOuterMeasure
          {M | Aligned P a bits p M}).toReal :=
      (FiniteUniformFibers.probability_eq_sum (Aligned P a bits p)).symm
    _ = ((Fintype.card F : ℝ)⁻¹ ^ 4) ^ b := hprob
    _ = 1 / (Fintype.card F : ℝ) ^ (4 * b) := by
      rw [← pow_mul, inv_pow, one_div]

theorem alignmentNormalization_proof : AlignmentNormalizationResult.{u} := by
  intro F _ _ _ b κ _ _ hκ P a ha bits p
  exact alignment_probability P hκ a ha bits p

theorem alignment_probability_pos {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) :
    0 < offsetProbability (Aligned P a bits p) := by
  rw [alignment_probability P hκ a ha bits p]
  positivity

end
end Balanced.Local

end OAI
