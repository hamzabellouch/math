import OAI.Probability.StrongRayleigh.MarginalBase

namespace OAI

universe u_1

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Topology ComplexConjugate
namespace Problem336AdditiveD139

lemma finiteMarginal_isDeterminantal {I : Type u_1} {K : I → I → ℂ}
    {μ : ProbabilityMeasure (I → Bool)} (hμ : IsDeterminantalLaw μ K)
    (S : Finset I) :
    IsFiniteDeterminantalLaw (finiteMarginal μ S) (fun i j : S => K i.1 j.1) := by
  classical
  intro A
  let emb : S ↪ I := ⟨Subtype.val, Subtype.val_injective⟩
  let T : Finset I := A.map emb
  let e : A ≃ T := Equiv.ofBijective
    (fun i => ⟨i.1.1, Finset.mem_map_of_mem emb i.2⟩)
    (by
      constructor
      · intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun x : T => (x : I)) hab
      · rintro ⟨i, hi⟩
        obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
        exact ⟨⟨j, hj⟩, rfl⟩)
  have hs : MeasurableSet {x : S → Bool | ∀ i ∈ A, x i = true} :=
    (Set.toFinite _).measurableSet
  rw [finiteMarginal, ProbabilityMeasure.map_apply' _
    (Measurable.of_eval (fun i => measurable_pi_apply i.1)).aemeasurable hs]
  have hevent : (fun x : I → Bool => fun i : S => x i.1) ⁻¹'
      {x : S → Bool | ∀ i ∈ A, x i = true} =
      {x : I → Bool | ∀ i ∈ T, x i = true} := by
    ext x
    simp [T, emb]
  rw [hevent, hμ T]
  convert (Matrix.det_submatrix_equiv_self e (fun i j : T => K i.1 j.1)).symm using 1
  congr 1

end Problem336AdditiveD139

end

end OAI
