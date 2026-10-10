import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanConeIdeal
import OAI.GroupTheory.PolycyclicRecognition.Algebra.QuotientWordBasis

namespace OAI

/-! # The positive trace character of a Cartan cone quotient

The coefficients come from an actual pure-word basis of the quotient.
The abelianization coordinates prove strict positivity for every inside
generator, including the extremal generators of a ray or a two-ray cone.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set
open scoped BigOperators

theorem bracketWordCount_eq_zero_of_pure
    {I : Type*} [DecidableEq I] (outside : I → Prop)
    {w : FreeMagma I} (hw : ¬IsMixedWord outside w) {i : I} (hi : outside i) :
    bracketWordCount w i = 0 := by
  induction w using FreeMagma.rec with
  | of j =>
    have hij : i ≠ j := fun h => hw (h ▸ hi)
    simp [bracketWordCount, hij]
  | mul u v hu hv =>
    exact Nat.add_eq_zero_iff.mpr ⟨hu (fun h => hw (Or.inl h)), hv (fun h => hw (Or.inr h))⟩

namespace CartanWordModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

/-- The same mixed ideal, viewed as a submodule for the actual Cartan action. -/
def coneCartanSubmodule (C : Set (H →ₗ[ℝ] ℝ))
    (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C) : LieSubmodule ℝ H (cartanRootIdeal H) :=
  { (M.coneWordIdeal C).toSubmodule with
    lie_mem := fun {h v} hv => M.coneWordIdeal_cartan_invariant C hadd h v hv }

/-- Trace on a pure-word quotient basis is the sum of the actual word
weights; generalized eigenspaces retain the nilpotent parts of the action. -/
theorem trace_cone_word_basis
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    {J : Type*} [Fintype J]
    (b : Basis J ℝ ((cartanRootIdeal H) ⧸ M.coneCartanSubmodule C hadd))
    (words : J → FreeMagma (Fin M.letterCount))
    (hwords : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ
      (evalBracketWord M.letter (words j)) = b j) (h : H) :
    LinearMap.trace ℝ ((cartanRootIdeal H) ⧸ M.coneCartanSubmodule C hadd)
      (toEnd ℝ H _ h) =
        ∑ i, ((∑ j, bracketWordCount (words j) i : ℕ) : ℝ) * M.weight i h := by
  let Q := (cartanRootIdeal H) ⧸ M.coneCartanSubmodule C hadd
  let q := LieSubmodule.Quotient.mk' (M.coneCartanSubmodule C hadd)
  let α := fun i => (M.weight i : H →ₗ[ℝ] ℝ)
  have hm (j : J) : b j ∈ genWeightSpace Q (bracketWordWeight α (words j)) := by
    rw [← hwords j]
    exact map_genWeightSpace_le q ⟨_,
      cartan_word_mem_genWeight H M.letter M.weight M.letter_root (words j), rfl⟩
  let ψ : J → Weight ℝ H Q := fun j =>
    { toFun := bracketWordWeight α (words j)
      genWeightSpace_ne_bot' := by
        intro hz
        have hh := hm j
        rw [hz] at hh
        exact b.ne_zero j hh }
  have ht := trace_eq_sum_of_generalizedWeight_basis b ψ hm h
  change LinearMap.trace ℝ Q (toEnd ℝ H Q h) =
    ∑ j, bracketWordWeight α (words j) h at ht
  rw [ht]
  simp_rw [bracketWordWeight_eq_count, Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

/-- The quotient trace is an integral combination of inside generator
weights, with strictly positive coefficients for every inside generator. -/
theorem exists_positive_cone_trace_coefficients
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C) :
    ∃ c : Fin M.letterCount → ℕ,
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C → c i = 0) ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C → 0 < c i) ∧
      ∀ h : H, LinearMap.trace ℝ
        ((cartanRootIdeal H) ⧸ M.coneCartanSubmodule C hadd) (toEnd ℝ H _ h) =
          ∑ i, (c i : ℝ) * M.weight i h := by
  classical
  let outside := fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C
  obtain ⟨b, words, hpure, hwords⟩ :=
    exists_pure_quotient_word_basis M.letter outside M.generates
  refine ⟨fun i => ∑ j, bracketWordCount (words j) i, ?_, ?_, ?_⟩
  · intro i hi
    exact Finset.sum_eq_zero (fun j _ => bracketWordCount_eq_zero_of_pure outside (hpure j) hi)
  · intro i hi
    let N := (lowerCentralSeries ℝ (cartanRootIdeal H) (cartanRootIdeal H) 1).toSubmodule
    apply positive_inside_quotient_word_counts M.letter outside M.generates N.mkQ ?_
      M.abelianBasis M.letter_quotient b words hwords i (not_not.mpr hi)
    intro x y
    apply (Submodule.Quotient.mk_eq_zero N).mpr
    change ⁅x, y⁆ ∈ lowerCentralSeries ℝ (cartanRootIdeal H) (cartanRootIdeal H) (0 + 1)
    rw [lowerCentralSeries_succ, lowerCentralSeries_zero]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) (LieSubmodule.mem_top y)
  · exact M.trace_cone_word_basis C hadd b words hwords

/-- The trace character descends to the canonical height space. -/
theorem exists_positive_cone_height_character {n : ℕ} (T : TriangularAdjoint L n)
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C) :
    ∃ (ℓ : HeightSpace T.character →ₗ[ℝ] ℝ) (c : Fin M.letterCount → ℕ),
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C → c i = 0) ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C → 0 < c i) ∧
      ℓ = ∑ i, (c i : ℝ) • cartanHeightWeight T H (M.weight i) ∧
      ∀ h : H, LinearMap.trace ℝ
        ((cartanRootIdeal H) ⧸ M.coneCartanSubmodule C hadd) (toEnd ℝ H _ h) =
          ℓ (heightProjection T.character (h : L)) := by
  obtain ⟨c, hout, hin, htrace⟩ := M.exists_positive_cone_trace_coefficients C hadd
  refine ⟨∑ i, (c i : ℝ) • cartanHeightWeight T H (M.weight i), c, hout, hin, rfl, ?_⟩
  intro h
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    cartanHeightWeight_projection] using htrace h

end CartanWordModel
end PolycyclicRecognition

end

end OAI
