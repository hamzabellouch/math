import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Tactic

namespace OAI

/-!
# Concrete operators for Kadison similarity

These definitions use bounded operators on the actual Hilbert space, and similarity
uses a unit of that bounded-operator algebra.  The compression estimate is the
operator calculation in Lemma `lem:compressed-commutator` of the manuscript.
-/

noncomputable section

namespace KadisonSimilarity

section Homomorphisms

variable (A H : Type*) [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A complex-linear unital algebra homomorphism which is bounded. -/
abbrev BoundedUnitalHom :=
  {π : A →ₐ[ℂ] (H →L[ℂ] H) // Continuous π}

/-- Similarity by a bounded invertible operator to an adjoint-preserving homomorphism. -/
def SimilarToStar (π : BoundedUnitalHom A H) : Prop :=
  ∃ S : (H →L[ℂ] H)ˣ, ∀ a : A,
    (S : H →L[ℂ] H) * π.1 (star a) * (↑S⁻¹ : H →L[ℂ] H) =
      star ((S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H))

/-- An already adjoint-preserving homomorphism requires no change of coordinates. -/
theorem similarToStar_of_star (π : BoundedUnitalHom A H)
    (hπ : ∀ a : A, π.1 (star a) = star (π.1 a)) : SimilarToStar A H π := by
  refine ⟨1, ?_⟩
  intro a
  simpa using hπ a

/-- The positive metric identity attached to a similarity. This is the algebraic
identity used in the completely bounded implementation argument. -/
theorem similarToStar_metric (π : BoundedUnitalHom A H) :
    SimilarToStar A H π ↔
      ∃ S : (H →L[ℂ] H)ˣ, ∀ a : A,
        (star (S : H →L[ℂ] H) * (S : H →L[ℂ] H)) * π.1 (star a) =
          star (π.1 a) * (star (S : H →L[ℂ] H) * (S : H →L[ℂ] H)) := by
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨S, ?_⟩
    intro a
    have h := congrArg (fun X : H →L[ℂ] H =>
      star (S : H →L[ℂ] H) * X * (S : H →L[ℂ] H)) (hS a)
    simpa only [star_mul, star_inv, mul_assoc, ← Units.coe_star_inv, ← Units.coe_star,
      Units.inv_mul, Units.mul_inv, Units.inv_mul_cancel_left,
      Units.mul_inv_cancel_left, mul_one, one_mul] using h
  · rintro ⟨S, hS⟩
    refine ⟨S, ?_⟩
    intro a
    have h := congrArg (fun X : H →L[ℂ] H =>
      star (↑S⁻¹ : H →L[ℂ] H) * X * (↑S⁻¹ : H →L[ℂ] H)) (hS a)
    simpa only [star_mul, star_inv, mul_assoc, ← Units.coe_star_inv, ← Units.coe_star,
      Units.inv_mul, Units.mul_inv, Units.inv_mul_cancel_left,
      Units.mul_inv_cancel_left, mul_one, one_mul] using h

end Homomorphisms

section Commutators

variable {R : Type*} [NormedRing R]

/-- The commutator, with the sign convention of the manuscript. -/
def commutator (S T : R) : R := S * T - T * S

@[simp] theorem commutator_zero_left (T : R) : commutator 0 T = 0 := by
  simp [commutator]

@[simp] theorem commutator_zero_right (T : R) : commutator T 0 = 0 := by
  simp [commutator]

theorem commutator_sub_left (S T U : R) :
    commutator (S - T) U = commutator S U - commutator T U := by
  simp only [commutator, sub_mul, mul_sub]
  abel

/-- Replacing an operator changes a commutator by at most twice its norm change. -/
theorem norm_commutator_le (S T : R) :
    ‖commutator S T‖ ≤ 2 * ‖S‖ * ‖T‖ := by
  calc
    ‖commutator S T‖ ≤ ‖S * T‖ + ‖T * S‖ := norm_sub_le _ _
    _ ≤ ‖S‖ * ‖T‖ + ‖T‖ * ‖S‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖S‖ * ‖T‖ := by ring

theorem norm_commutator_sub_le (S T U : R) :
    ‖commutator S U - commutator T U‖ ≤ 2 * ‖S - T‖ * ‖U‖ := by
  rw [← commutator_sub_left]
  exact norm_commutator_le _ _

/-- The perturbation estimate used when restoring the original operator after averaging. -/
theorem norm_commutator_le_of_approx (S T U : R) {a d : ℝ}
    (hT : ‖commutator T U‖ ≤ a) (hST : ‖S - T‖ ≤ d) :
    ‖commutator S U‖ ≤ a + 2 * d * ‖U‖ := by
  calc
    ‖commutator S U‖ ≤ ‖commutator T U‖ + ‖commutator S U - commutator T U‖ :=
      norm_le_insert' _ _
    _ ≤ a + 2 * ‖S - T‖ * ‖U‖ := add_le_add hT (norm_commutator_sub_le _ _ _)
    _ ≤ a + 2 * d * ‖U‖ := by gcongr

end Commutators

section Compression

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

open ContinuousLinearMap

/-- Exact compression identity, including both full-codomain errors. -/
theorem compression_commutator_identity (G T : H →L[ℂ] H)
    (J : K →L[ℂ] K) (ι : K →L[ℂ] H) :
    commutator J (ι.adjoint.comp (T.comp ι)) =
      ι.adjoint.comp ((commutator G T).comp ι) -
        (G.adjoint.comp ι - ι.comp J.adjoint).adjoint.comp (T.comp ι) +
        ι.adjoint.comp (T.comp (G.comp ι - ι.comp J)) := by
  simp only [map_sub, adjoint_comp, adjoint_adjoint, sub_comp, comp_sub,
    comp_assoc, commutator, mul_def]
  abel

/-- Lemma `lem:compressed-commutator`: a contractive inclusion transfers a
commutator estimate, with one contribution from each intertwining error. -/
theorem norm_compressed_commutator_le (G T : H →L[ℂ] H)
    (J : K →L[ℂ] K) (ι : K →L[ℂ] H) {ε η : ℝ}
    (hι : ‖ι‖ ≤ 1)
    (hG : ‖commutator G T‖ ≤ ε * ‖T‖)
    (hR : ‖G.comp ι - ι.comp J‖ ≤ η)
    (hR' : ‖G.adjoint.comp ι - ι.comp J.adjoint‖ ≤ η) :
    ‖commutator J (ι.adjoint.comp (T.comp ι))‖ ≤ (ε + 2 * η) * ‖T‖ := by
  have hε : 0 ≤ ε * ‖T‖ := (norm_nonneg _).trans hG
  have hη : 0 ≤ η := (norm_nonneg _).trans hR
  have hfirst : ‖ι.adjoint.comp ((commutator G T).comp ι)‖ ≤ ε * ‖T‖ := by
    calc
      _ ≤ ‖ι.adjoint‖ * (‖commutator G T‖ * ‖ι‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
          (opNorm_comp_le _ _) (norm_nonneg _))
      _ = ‖ι‖ * (‖commutator G T‖ * ‖ι‖) := by rw [adjoint.norm_map]
      _ ≤ 1 * (ε * ‖T‖ * 1) := by gcongr
      _ = ε * ‖T‖ := by ring
  have hsecond :
      ‖(G.adjoint.comp ι - ι.comp J.adjoint).adjoint.comp (T.comp ι)‖ ≤
        η * ‖T‖ := by
    calc
      _ ≤ ‖(G.adjoint.comp ι - ι.comp J.adjoint).adjoint‖ * (‖T‖ * ‖ι‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
          (opNorm_comp_le _ _) (norm_nonneg _))
      _ = ‖G.adjoint.comp ι - ι.comp J.adjoint‖ * (‖T‖ * ‖ι‖) := by
        rw [adjoint.norm_map]
      _ ≤ η * (‖T‖ * 1) := by gcongr
      _ = η * ‖T‖ := by ring
  have hthird : ‖ι.adjoint.comp (T.comp (G.comp ι - ι.comp J))‖ ≤ η * ‖T‖ := by
    calc
      _ ≤ ‖ι.adjoint‖ * (‖T‖ * ‖G.comp ι - ι.comp J‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
          (opNorm_comp_le _ _) (norm_nonneg _))
      _ = ‖ι‖ * (‖T‖ * ‖G.comp ι - ι.comp J‖) := by rw [adjoint.norm_map]
      _ ≤ 1 * (‖T‖ * η) := by gcongr
      _ = η * ‖T‖ := by ring
  rw [compression_commutator_identity]
  calc
    _ ≤ (‖ι.adjoint.comp ((commutator G T).comp ι)‖ +
        ‖(G.adjoint.comp ι - ι.comp J.adjoint).adjoint.comp (T.comp ι)‖) +
        ‖ι.adjoint.comp (T.comp (G.comp ι - ι.comp J))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (ε * ‖T‖ + η * ‖T‖) + η * ‖T‖ :=
      add_le_add (add_le_add hfirst hsecond) hthird
    _ = (ε + 2 * η) * ‖T‖ := by ring

/-- The manuscript's constant after the two propagation errors are substituted. -/
theorem norm_compressed_commutator_le_paper (G T : H →L[ℂ] H)
    (J : K →L[ℂ] K) (ι : K →L[ℂ] H) {ε c₀ : ℝ}
    (hι : ‖ι‖ ≤ 1)
    (hG : ‖commutator G T‖ ≤ ε * ‖T‖)
    (hR : ‖G.comp ι - ι.comp J‖ ≤ 2 * c₀ * ε)
    (hR' : ‖G.adjoint.comp ι - ι.comp J.adjoint‖ ≤ 2 * c₀ * ε) :
    ‖commutator J (ι.adjoint.comp (T.comp ι))‖ ≤ (1 + 4 * c₀) * ε * ‖T‖ := by
  convert norm_compressed_commutator_le G T J ι hι hG hR hR' using 1
  ring

end Compression

end KadisonSimilarity

end

end OAI
