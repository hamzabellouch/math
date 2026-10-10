import OAI.Analysis.BoundedHochschild.CompleteAdditivity

namespace OAI

/-! Support projections for completely additive positive functionals. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Complete additivity supplies a support projection without assuming
normality in advance. This is used in proving the normality criterion. -/
theorem exists_additive_positive_support (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (ψ : M →ₚ[ℂ] ℂ) (hψ : CompletelyAdditive (positiveFunctionalCLM ψ)) :
    ∃ p : M, IsStarProjection p ∧ ψ p = ψ 1 ∧
      ∀ q : M, IsStarProjection q → q ≤ p → ψ q = 0 → q = 0 := by
  classical
  let A : Set (Set M) := {S | (∀ p ∈ S, IsStarProjection p ∧ p ≠ 0 ∧ ψ p = 0) ∧
    ∀ p ∈ S, ∀ q ∈ S, p ≠ q → p * q = 0}
  obtain ⟨S, hS⟩ := zorn_subset A (fun c hc hchain => by
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · intro p hp
      obtain ⟨s, hs, hps⟩ := Set.mem_sUnion.mp hp
      exact (hc hs).1 p hps
    · intro p hp q hq hpq
      obtain ⟨s, hs, hps⟩ := Set.mem_sUnion.mp hp
      obtain ⟨t, ht, hqt⟩ := Set.mem_sUnion.mp hq
      rcases hchain.total hs ht with hst | hts
      · exact (hc ht).2 p (hst hps) q hqt hpq
      · exact (hc hs).2 p hps q (hts hqt) hpq)
  let f : S → M := Subtype.val
  have hf (i : S) : IsStarProjection (f i) := (hS.1.1 i i.property).1
  have ho (i j : S) (hij : i ≠ j) : f i * f j = 0 :=
    hS.1.2 i i.property j j.property (fun h => hij (Subtype.ext h))
  obtain ⟨P, hP, hPu, hPl, _⟩ := exists_orthogonal_projection_sum e f hf ho
  have hPnull : ψ P = 0 := by
    have ht := hψ S f hf ho P hP hPu hPl
    have heq : (fun s : Finset S => ∑ i ∈ s, positiveFunctionalCLM ψ (f i)) =
        (fun _ : Finset S => (0 : ℂ)) := by
      funext s
      apply Finset.sum_eq_zero
      intro i _
      exact (hS.1.1 i i.property).2.2
    rw [heq] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  refine ⟨1 - P, hP.one_sub, ?_, ?_⟩
  · rw [map_sub, hPnull, sub_zero]
  · intro q hq hqP hnull
    by_contra hq0
    have hPq : P * q = 0 :=
      HochschildTypeII.projection_orthogonal_of_le_complement hP hq hqP
    have hfq (i : S) : f i * q = 0 := by
      calc
        f i * q = (f i * P) * q := by rw [((hf i).le_iff_mul_eq_left hP).mp (hPu i)]
        _ = 0 := by rw [mul_assoc, hPq, mul_zero]
    have hqf (i : S) : q * f i = 0 := by
      simpa only [star_mul, (hf i).isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq,
        star_zero] using congrArg star (hfq i)
    have hnew : insert q S ∈ A := by
      constructor
      · intro a ha
        rcases Set.mem_insert_iff.mp ha with rfl | ha
        · exact ⟨hq, hq0, hnull⟩
        · exact hS.1.1 a ha
      · intro a ha b hb hab
        rcases Set.mem_insert_iff.mp ha with har | ha
        · subst a
          rcases Set.mem_insert_iff.mp hb with hbr | hb
          · exact (hab hbr.symm).elim
          · exact hqf ⟨b, hb⟩
        · rcases Set.mem_insert_iff.mp hb with hbr | hb
          · subst b
            exact hfq ⟨a, ha⟩
          · exact hS.1.2 a ha b hb hab
    have hsubset : insert q S ⊆ S := hS.2 hnew (Set.subset_insert q S)
    have hqin : q ∈ S := hsubset (Set.mem_insert q S)
    exact hq0 (by simpa only [f, hq.isIdempotentElem.eq] using hfq ⟨q, hqin⟩)

end KadisonRingrose
end BoundedHochschild

end

end OAI
