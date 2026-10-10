import OAI.GroupTheory.PolycyclicRecognition.Analysis.RegularWalkHarmonic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

namespace OAI

/-! # An infinite real linear image of an infinite polynomial-growth group

This is the linear-representation conclusion in Kleiner, JAMS 23 (2010),
Sections 4 and 5. Both the harmonic finite-dimensionality and the nonconstant
harmonic-function construction are proved here, rather than assumed.
-/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type*} [Group G] [DecidableEq G] [Infinite G]

theorem infinite_generating_finset_nonempty (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set G) = ⊤) : S.Nonempty := by
  by_contra h
  have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  obtain ⟨y, hy, hy'⟩ := exists_wordBall_escape S hS hgen 0
  simp [he, wordBall] at hy hy'
  exact hy' hy

theorem polynomial_growth_infinite_real_linear_image
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C b : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ b) :
    ∃ n : ℕ, ∃ ρ : G →* Matrix.GeneralLinearGroup (Fin n) ℝ, (Set.range ρ).Infinite := by
  obtain ⟨C, b, hC⟩ := hvol
  have hCpos : 0 < (C : ℝ) := by
    have h := hC 0
    have hc : 1 ≤ C := by simpa [wordBall_zero] using h
    exact Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hc)
  have hvol' (n : ℕ) : ((wordBall S n).card : ℝ) ≤ C * (1 + (n : ℝ)) ^ b := by
    exact_mod_cast hC n
  have hne := infinite_generating_finset_nonempty S hS hgen
  let V := polynomialHarmonicFunctions S 1
  let : Module.Finite ℝ V :=
    polynomialHarmonicFunctions_finite_of_word_growth S hS hgen 1 C b hC
  let n := Module.finrank ℝ V
  let e : (V ≃ₗ[ℝ] V) ≃* Matrix.GeneralLinearGroup (Fin n) ℝ :=
    ((Matrix.GeneralLinearGroup.toLin' (Module.finBasis ℝ V)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ V)).symm
  let ρ := polynomialHarmonicRepresentation S hS hgen 1
  refine ⟨n, e.toMonoidHom.comp ρ, ?_⟩
  have hinf := polynomial_growth_harmonic_representation_infinite S hne hS hgen hCpos b hvol'
  have hi := hinf.image e.injective.injOn
  simpa only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Set.range_comp] using hi

end PolycyclicRecognition

end

end OAI
