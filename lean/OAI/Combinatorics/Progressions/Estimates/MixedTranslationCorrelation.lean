import OAI.Combinatorics.Progressions.Estimates.NativeBinaryAssignments

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_mixed_translation_transfer (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p),
      ∃ E : NativeIntegerVectorEquivalence s ((p + C) ^ C)
          (fun k (x : Fin 3 → ℤ) => V.eval k (fun j => correlationInput (x 0) (x 1 + x 2) j.1))
          (fun a x => coordinateTranslationExpansion V.eval (mixedTranslationCoordinates s) a
            (mixedTranslationSample s x)),
        ∀ {X : Type*} (S : Finset X) (sample : X → Fin 3 → ℤ) (k : Fin V.outputDim)
          (f : X → ℂ) (q : ℝ),
          Real.exp (-q) ≤ ‖𝔼 u ∈ S, f u * star
            (V.eval k (fun j => correlationInput (sample u 0) (sample u 1 + sample u 2) j.1))‖ →
          ∃ (a : BinaryTensorIndex (Fin V.outputDim) (mixedTranslationCoordinates s).length)
            (b : Fin (E.selectedExpansion k a).count),
            Real.exp (-(q + 2 * (p + C) ^ C)) ≤ ‖𝔼 u ∈ S, f u * star
              (V.eval (firstTranslationCoordinate (mixedTranslationCoordinates s) a)
                  (fun j => correlationInput (sample u 0) (sample u 1) j.1) *
                translationExpansionRemainder V.eval (mixedTranslationCoordinates s) a
                  (mixedTranslationSample s (sample u)) *
                ((E.selectedExpansion k a).test b).eval (sample u))‖ := by
  obtain ⟨C, hC, hexpand⟩ := exists_mixed_translation_equivalence s
  refine ⟨C, hC, ?_⟩
  intro p V
  let E := hexpand V
  refine ⟨E, ?_⟩
  intro X S sample k f q hcorr
  obtain ⟨a, b, hab⟩ := E.transfer_sample_correlation S sample k f
    (fun u _ => coordinateTranslationExpansion_unit V.eval V.unit_eval
      (mixedTranslationCoordinates s) (mixedTranslationSample s (sample u))) hcorr
  refine ⟨a, b, ?_⟩
  simpa only [V.mixedTranslationExpansion_factor, star_mul, mul_assoc, mul_left_comm, mul_comm] using hab

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
