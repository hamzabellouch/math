import OAI.GroupTheory.PolycyclicRecognition.Algebra.SemisimpleInnerFixedRepresentative

namespace OAI

/-! # Simultaneous fixed representatives for commuting semisimple factors

Successive canonical projections preserve all previously fixed symmetries.
Every inner automorphism centralizing a finite commuting semisimple family
therefore has a representative fixed by the whole family.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

theorem commuting_semisimple_inner_fixed_representative
    (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (hss : ∀ S ∈ ss, Module.End.IsSemisimple S.toLinearMap)
    (hpair : ∀ S ∈ ss, ∀ T ∈ ss, Commute S.toLinearMap T.toLinearMap)
    (x : L) (hx : ∀ S ∈ ss, Commute S.toLinearMap (polynomialInnerLieEquiv x).toLinearMap) :
    ∃ y : L, (∀ S ∈ ss, S y = y) ∧
      (polynomialInnerLieEquiv y).toLinearMap = (polynomialInnerLieEquiv x).toLinearMap ∧
      ∀ T : L ≃ₗ⁅ℝ⁆ L, (∀ S ∈ ss, Commute T.toLinearMap S.toLinearMap) →
        T x = x → T y = y := by
  induction ss generalizing x with
  | nil => exact ⟨x, by simp, rfl, fun _ _ ht => ht⟩
  | cons S ss ih =>
    have hhead : S ∈ S :: ss := by simp
    have hmem {T : L ≃ₗ⁅ℝ⁆ L} (ht : T ∈ ss) : T ∈ S :: ss := List.mem_cons_of_mem S ht
    obtain ⟨y, hy, hiy, hpres⟩ :=
      semisimple_inner_fixed_representative_preserves S (hss S hhead) x (hx S hhead)
    obtain ⟨z, hz, hiz, hpz⟩ := ih
      (fun T ht => hss T (hmem ht))
      (fun T ht U hu => hpair T (hmem ht) U (hmem hu)) y
      (fun T ht => by rw [hiy]; exact hx T (hmem ht))
    refine ⟨z, ?_, hiz.trans hiy, ?_⟩
    · intro T ht
      rcases List.mem_cons.mp ht with h | ht
      · subst T
        exact hpz S (fun T ht => hpair S hhead T (hmem ht)) hy
      · exact hz T ht
    · intro T hT hTx
      have hTy : T y = y := hpres T (hT S hhead) hTx
      exact hpz T (fun U hu => hT U (hmem hu)) hTy

end PolycyclicRecognition

end

end OAI
