import OAI.GroupTheory.PolycyclicRecognition.Geometry.SolvableWeightEigenvectors
import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordLengthFiltration
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FilteredPolynomialPerturbation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SplitAnnihilator

namespace OAI

/-! # Real split annihilators for the faithful solvable representation

The semisimple derivation preserves word length, while left multiplication
raises it. The finite word-length filtration therefore turns the split
annihilator of the derivation into one for their sum.
-/

noncomputable section
namespace PolycyclicRecognition

open Polynomial Module

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

local notation "K" => CartanNilshadow T H
local notation "Q" c => TruncatedEnvelopingAlgebra ℝ K c

theorem solvableTruncatedRepresentation_split_annihilator (c : ℕ) (x : L) :
    ∃ p : ℝ[X], p.Monic ∧ p.Splits ∧
      aeval (solvableTruncatedRepresentation T H c x) p = 0 := by
  let := finiteDimensional_truncatedEnvelopingAlgebra (finBasis ℝ K) c
  let j := truncatedEnvelopingGenerator (R := ℝ) (L := K) c
  let δ := nilshadowWeightDerivation T H x
  let D := truncatedEnvelopingDerivation c δ
  let N := truncatedLeftRepresentation (R := ℝ) c (cartanNilshadowEquiv T H x)
  let B := wordLengthSpan j
  have hgen : Algebra.adjoin ℝ (Set.range j) = ⊤ := by
    apply top_unique
    rw [← truncatedEnveloping_adjoin_basis (finBasis ℝ K) c]
    apply Algebra.adjoin_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨finBasis ℝ K i, rfl⟩
  have hD (k : ℕ) (v : Q c) (hv : v ∈ B k) : D v ∈ B k :=
    wordLengthSpan_derivative j D δ (truncatedEnvelopingDerivation_mul c δ)
      (truncatedEnvelopingDerivation_one c δ)
      (truncatedEnvelopingDerivation_generator c δ) k hv
  have hN (k : ℕ) (v : Q c) (hv : v ∈ B k) : N v ∈ B (k + 1) :=
    wordLengthSpan_generator_mul j k (cartanNilshadowEquiv T H x) hv
  let p := realEigenPolynomial D
  have hp : aeval D p = 0 := realEigenPolynomial_annihilates D
    (solvableWeightDerivation_eigenspaces_span T H c x)
  refine ⟨p ^ c, (realEigenPolynomial_monic D).pow c,
    (realEigenPolynomial_splits D).pow c, ?_⟩
  have heq : solvableTruncatedRepresentation T H c x = D + N := by
    change N + D = D + N
    exact add_comm _ _
  rw [heq]
  exact filtered_polynomial_annihilator B D N (wordLengthSpan_antitone j) hD hN c
    (wordLengthSpan_zero_eq_top j hgen)
    (wordLengthSpan_eq_bot j c (truncatedEnvelopingGenerator_prod_eq_zero c)) p hp

theorem solvableTruncatedRepresentation_genEigenspaces_span (c : ℕ) (x : L) :
    ⨆ r : ℝ, (solvableTruncatedRepresentation T H c x).maxGenEigenspace r = ⊤ := by
  let := finiteDimensional_truncatedEnvelopingAlgebra (finBasis ℝ K) c
  obtain ⟨p, hm, hs, hz⟩ := solvableTruncatedRepresentation_split_annihilator T H c x
  exact iSup_maxGenEigenspace_eq_top_of_split_annihilator _ p hm.ne_zero hs hz

end PolycyclicRecognition

end

end OAI
