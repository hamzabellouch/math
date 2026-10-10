import OAI.Analysis.KadisonSimilarity.Representation.ConcretePredualDuality
import OAI.Analysis.KadisonSimilarity.Representation.ProperlyInfiniteEstimate
import OAI.Analysis.KadisonSimilarity.Derivation.DicksonDischarge
import OAI.Analysis.BoundedHochschild.ProperlyInfiniteIsometries

namespace OAI

/-! Two orthogonal isometries yield every finite internal isometry row.
The concrete Banach predual supplies the structural existence theorem. -/

noncomputable section
namespace KadisonSimilarity

private def binaryIsometryFamily {A : Type*} [Monoid A] (v w : A) : ℕ → A
  | 0 => w
  | n + 1 => v * binaryIsometryFamily v w n

private theorem binaryIsometryFamily_orthogonal {A : Type*} [Ring A] [StarRing A]
    (v w : A) (hv : star v * v = 1) (hw : star w * w = 1)
    (hvw : star v * w = 0) :
    ∀ i j, star (binaryIsometryFamily v w i) * binaryIsometryFamily v w j =
      if i = j then 1 else 0 := by
  have hwv : star w * v = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hvw
  intro i
  induction i with
  | zero =>
      intro j
      cases j with
      | zero => simpa only [binaryIsometryFamily, ite_true] using hw
      | succ j =>
          simp only [binaryIsometryFamily, Nat.zero_ne_add_one, ite_false,
            ← mul_assoc, hwv, zero_mul]
  | succ i ih =>
      intro j
      cases j with
      | zero =>
          simp only [binaryIsometryFamily, Nat.add_one_ne_zero, ite_false,
            star_mul, mul_assoc, hvw, mul_zero]
      | succ j =>
          rw [show binaryIsometryFamily v w (i + 1) = v * binaryIsometryFamily v w i
            from rfl, show binaryIsometryFamily v w (j + 1) =
              v * binaryIsometryFamily v w j from rfl, star_mul]
          calc
            (star (binaryIsometryFamily v w i) * star v) *
                (v * binaryIsometryFamily v w j) =
              star (binaryIsometryFamily v w i) *
                ((star v * v) * binaryIsometryFamily v w j) := by noncomm_ring
            _ = if i + 1 = j + 1 then 1 else 0 := by
              rw [hv, one_mul, ih]
              simp only [Nat.add_right_cancel_iff]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : VonNeumannAlgebra H)

local instance infiniteStructureClosed : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (P : Set (H →L[ℂ] H))
  infer_instance

theorem internal_isometry_rows_of_no_finite_central_summand
    (hno : BoundedHochschild.KadisonRingrose.NoFiniteCentralSummand P.toStarSubalgebra) :
    HasInternalIsometryRows P := by
  obtain ⟨v, w, hv, hw, hvw⟩ :=
    BoundedHochschild.KadisonRingrose.exists_two_orthogonal_isometries
      (concretePredualEquiv P) hno
  intro n
  refine ⟨fun i => binaryIsometryFamily v w i.val, fun i j => ?_⟩
  simpa only [Fin.val_inj] using binaryIsometryFamily_orthogonal v w hv hw hvw i.val j.val

open BoundedHochschild.KadisonRingrose HochschildCorners
open scoped ComplexOrder

theorem central_projection_zero_or_one {A : Type*} [CStarAlgebra A] [Nontrivial A]
    (hfactor : ∀ a : A, (∀ b, a * b = b * a) → ∃ c : ℂ, a = algebraMap ℂ A c)
    (p : A) (hp : IsStarProjection p) (hc : ∀ a, p * a = a * p) : p = 0 ∨ p = 1 := by
  obtain ⟨c, hpc⟩ := hfactor p hc
  have hcc : c * c = c := by
    apply FaithfulSMul.algebraMap_injective ℂ A
    rw [map_mul]
    simpa only [hpc] using hp.isIdempotentElem.eq
  have hz : c * (c - 1) = 0 := by rw [mul_sub, mul_one, hcc, sub_self]
  rcases mul_eq_zero.mp hz with hc0 | hc1
  · left
    rw [hpc, hc0, map_zero]
  · right
    rw [hpc, sub_eq_zero.mp hc1, map_one]

theorem no_finite_central_summand_of_infinite_factor
    (hfactor : ∀ a : P.toStarSubalgebra, (∀ b, a * b = b * a) →
      ∃ c : ℂ, a = algebraMap ℂ P.toStarSubalgebra c)
    (hinfinite : ¬ FiniteAlgebra P.toStarSubalgebra) :
    NoFiniteCentralSummand P.toStarSubalgebra := by
  have hex : ∃ a : P.toStarSubalgebra, star a * a = 1 ∧ a * star a ≠ 1 := by
    simpa only [FiniteAlgebra, not_forall, not_imp, exists_prop] using hinfinite
  obtain ⟨a, _, ha⟩ := hex
  let : Nontrivial P.toStarSubalgebra := nontrivial_of_ne (a * star a) 1 ha
  intro p hp hcentral hfinite
  rcases central_projection_zero_or_one hfactor p hp hcentral with hz | hunit
  · exact hz
  · subst p
    exfalso
    apply hinfinite
    intro b hb
    let bC : Corner (1 : P.toStarSubalgebra) hp := ⟨b, by
      change 1 * b = b ∧ b * 1 = b
      simp⟩
    have hbC : star bC * bC = 1 := Subtype.ext hb
    exact congrArg (fun c : Corner (1 : P.toStarSubalgebra) hp =>
      (c : P.toStarSubalgebra)) (hfinite bC hbC)

theorem internal_isometry_rows_of_infinite_factor
    (hfactor : ∀ a : P.toStarSubalgebra, (∀ b, a * b = b * a) →
      ∃ c : ℂ, a = algebraMap ℂ P.toStarSubalgebra c)
    (hinfinite : ¬ FiniteAlgebra P.toStarSubalgebra) : HasInternalIsometryRows P :=
  internal_isometry_rows_of_no_finite_central_summand P
    (no_finite_central_summand_of_infinite_factor P hfactor hinfinite)

/-- A properly infinite factor satisfies the complete commutator estimate. -/
theorem infinite_factor_commutatorEstimate
    (hfactor : ∀ a : P.toStarSubalgebra, (∀ b, a * b = b * a) →
      ∃ c : ℂ, a = algebraMap ℂ P.toStarSubalgebra c)
    (hinfinite : ¬ FiniteAlgebra P.toStarSubalgebra) :
    CommutatorEstimate P (1 + 2 * (4 * Real.sqrt 2)) :=
  properlyInfinite_commutatorEstimate P
    (internal_isometry_rows_of_infinite_factor P hfactor hinfinite) dicksonTwoBound_proved

end KadisonSimilarity

end

end OAI
