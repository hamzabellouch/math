import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWordBasis
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTrace
import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightBasisTrace

namespace OAI

/-! # Balanced letter counts for actual Cartan word bases

The trace calculation is valid for generalized roots: no diagonalizability
or triangularity of the chosen word basis is assumed.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule Module
open scoped BigOperators

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
  (X : I → cartanRootIdeal H) (χ : I → Weight ℝ H L)
  (hX : ∀ i, (X i : L) ∈ rootSpace H (χ i))

include hX

theorem cartan_word_mem_genWeight (w : FreeMagma I) :
    evalBracketWord X w ∈ genWeightSpace (cartanRootIdeal H)
      (bracketWordWeight (fun i => (χ i : H →ₗ[ℝ] ℝ)) w) := by
  let α := fun i => (χ i : H →ₗ[ℝ] ℝ)
  have hm : evalBracketWord (fun i => (X i : L)) w ∈
      genWeightSpace L (bracketWordWeight α w) := by
    apply (mem_genWeightSpace L _ _).mpr
    intro h
    have hi (i : I) (h : H) : (X i : L) ∈
        (ad ℝ L h).maxGenEigenspace (α i h) :=
      genWeightSpace_le_genWeightSpaceOf L h (χ i) (hX i)
    have hw := evalBracketWord_mem_generalizedWeight H α (fun i => (X i : L)) hi w h
    change evalBracketWord (fun i => (X i : L)) w ∈
      (toEnd ℝ H L h).maxGenEigenspace (bracketWordWeight α w h) at hw
    simpa only [Module.End.mem_maxGenEigenspace] using hw
  let ι : (cartanRootIdeal H) →ₗ⁅ℝ,H⁆ L := ((cartanRootIdeal H).restr H).incl
  rw [← comap_genWeightSpace_eq_of_injective (f := ι)
    ((cartanRootIdeal H).restr H).injective_incl]
  change ι (evalBracketWord X w) ∈ genWeightSpace L (bracketWordWeight α w)
  change (cartanRootIdeal H).incl (evalBracketWord X w) ∈ _
  rw [evalBracketWord_map]
  exact hm

variable [Fintype I] [DecidableEq I]

/-- The trace character on the ideal is the sum of the actual letter weights,
counted with their occurrences in the selected word basis. -/
theorem trace_cartan_word_basis {J : Type*} [Fintype J]
    (b : Basis J ℝ (cartanRootIdeal H)) (words : J → FreeMagma I)
    (hwords : ∀ j, evalBracketWord X (words j) = b j) (h : H) :
    LinearMap.trace ℝ (cartanRootIdeal H) (toEnd ℝ H (cartanRootIdeal H) h) =
      ∑ i, ((∑ j, bracketWordCount (words j) i : ℕ) : ℝ) * χ i h := by
  let α := fun i => (χ i : H →ₗ[ℝ] ℝ)
  have hm (j : J) : b j ∈ genWeightSpace (cartanRootIdeal H)
      (bracketWordWeight α (words j)) := by
    rw [← hwords j]
    exact cartan_word_mem_genWeight H X χ hX (words j)
  let ψ : J → Weight ℝ H (cartanRootIdeal H) := fun j =>
    { toFun := bracketWordWeight α (words j)
      genWeightSpace_ne_bot' := by
        intro hz
        have hh := hm j
        rw [hz] at hh
        change b j = 0 at hh
        exact b.ne_zero j hh }
  have ht := trace_eq_sum_of_generalizedWeight_basis b ψ hm h
  change LinearMap.trace ℝ (cartanRootIdeal H) (toEnd ℝ H (cartanRootIdeal H) h) =
    ∑ j, bracketWordWeight α (words j) h at ht
  rw [ht]
  simp_rw [bracketWordWeight_eq_count, Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem balanced_cartan_word_counts {n : ℕ} (T : TriangularAdjoint L n)
    {J : Type*} [Fintype J]
    (b : Basis J ℝ (cartanRootIdeal H)) (words : J → FreeMagma I)
    (hwords : ∀ j, evalBracketWord X (words j) = b j)
    (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
    (w : HeightSpace T.character) :
    ∑ i, ((∑ j, bracketWordCount (words j) i : ℕ) : ℝ) *
      cartanHeightWeight T H (χ i) w = 0 := by
  have ht := (trace_cartan_word_basis H X χ hX b words hwords
    (cartanHeightSection T H w)).symm.trans
      (trace_cartanRootIdeal_eq_zero T H hunimod (cartanHeightSection T H w))
  exact ht

end PolycyclicRecognition

end

end OAI
