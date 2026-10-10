import OAI.Analysis.KadisonKastler.TypeIIIMatrixCorner
import OAI.Analysis.KadisonKastler.CornerFactorStructure
import OAI.Analysis.FactorGeneration.FiniteComparison

namespace OAI

/-! # Countable copies of a full projection

Blackadar, *Operator Algebras*, III.1.3.6 (author PDF, printed p.243),
asserts that a full projection in a properly infinite, locally countably
 decomposable von Neumann algebra admits a countable orthogonal family of
 equivalent projections with strong sum one. Separably acting algebras are
 countably decomposable. The input below is only this projection assertion.

The projection's central support is the already constructed orbit-closure
projection. Proper infiniteness is expressed by two isometries with
orthogonal ranges. No trace, corner type, or perturbation conclusion is part
of this published input.

Primary source: https://bruceblackadar.com/Mathematics/Cycr.pdf
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- The ordinary two-isometry description of a nonzero properly infinite
identity. The cross product states that the two range projections are orthogonal. -/
structure ProperlyInfiniteIdentity (M : VonNeumannAlgebra H) : Prop where
  nonzero : (1 : H →L[ℂ] H) ≠ 0
  isometries : ∃ v w : Algebra M,
    star v * v = 1 ∧ star w * w = 1 ∧ star v * w = 0

/-- Actual equivalent projection copies and their strong sum. -/
structure CountableProjectionCopies (M : VonNeumannAlgebra H) (p : AlgebraProjection M) where
  projection : ℕ → AlgebraProjection M
  witness : ℕ → Algebra M
  initial : ∀ i, star (witness i) * witness i = p.val
  final : ∀ i, witness i * star (witness i) = (projection i).val
  orthogonal : Pairwise (fun i j => (projection i).val * (projection j).val = 0)
  total : ∀ x : H, HasSum (fun i => ((projection i).val : H →L[ℂ] H) x) x

/-- Blackadar III.1.3.6 restricted to separably acting algebras. -/
def PublishedProperInfiniteProjectionCopies : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H], ∀ M : VonNeumannAlgebra H,
    ProperlyInfiniteIdentity M → ∀ p : AlgebraProjection M,
      (centralSupport p).val = 1 → Nonempty (CountableProjectionCopies M p)

/-- Finiteness is preserved by Murray--von Neumann equivalence. -/
theorem finiteProjectionIn_of_equivalent (p q : AlgebraProjection M)
    (hfinite : FiniteProjectionIn M p.val) (v : Algebra M)
    (hvi : star v * v = p.val) (hvf : v * star v = q.val) :
    FiniteProjectionIn M q.val := by
  let V : PartialIsometry M := ⟨p, v, hvi⟩
  have hvp : v * p.val = v := V.mul_support
  have hqv : q.val * v = v := by
    have ht := V.target_mul
    change (v * star v) * v = v at ht
    rwa [hvf] at ht
  have hps : p.val * star v = star v := by
    simpa only [star_mul, star_star, p.property.isSelfAdjoint.star_eq] using
      congrArg star hvp
  have hsq : star v * q.val = star v := by
    simpa only [star_mul, star_star, q.property.isSelfAdjoint.star_eq] using
      congrArg star hqv
  intro w hwi hqw
  have hws : star w * q.val = star w := by
    simpa only [star_mul, q.property.isSelfAdjoint.star_eq] using congrArg star hqw
  let a : Algebra M := star v * w * v
  have hai : star a * a = p.val := by
    change star (star v * w * v) * (star v * w * v) = p.val
    rw [star_mul, star_mul, star_star]
    calc
      _ = star v * star w * (v * star v) * w * v := by noncomm_ring
      _ = star v * (star w * q.val) * w * v := by rw [hvf]; noncomm_ring
      _ = star v * (star w * w) * v := by rw [hws]; noncomm_ring
      _ = p.val := by rw [hwi, hsq, hvi]
  have hpa : p.val * a = a := by
    change p.val * (star v * w * v) = star v * w * v
    rw [← mul_assoc, ← mul_assoc, hps]
  have haa := hfinite a hai hpa
  have hrec : v * (a * star a) * star v = w * star w := by
    change v * ((star v * w * v) * star (star v * w * v)) * star v = w * star w
    rw [star_mul, star_mul, star_star]
    calc
      _ = (v * star v) * w * (v * star v) * star w * (v * star v) := by noncomm_ring
      _ = q.val * w * q.val * star w * q.val := by rw [hvf]
      _ = w * (q.val * star w) * q.val := by rw [hqw]; noncomm_ring
      _ = w * star w := by
        have hwq : w * q.val = w := (show PartialIsometry M from ⟨q, w, hwi⟩).mul_support
        rw [← mul_assoc, hwq, mul_assoc, hws]
  calc
    w * star w = v * (a * star a) * star v := hrec.symm
    _ = q.val := by rw [haa, hvp, hvf]

namespace CountableProjectionCopies

variable {p : AlgebraProjection M} (D : CountableProjectionCopies M p)

private def rebasedPartial (i : ℕ) : Algebra M := D.witness i * star (D.witness 0)

private theorem rebased_initial (i : ℕ) :
    star (D.rebasedPartial i) * D.rebasedPartial i = (D.projection 0).val := by
  let V : PartialIsometry M := ⟨p, D.witness 0, D.initial 0⟩
  change star (D.witness i * star (D.witness 0)) *
    (D.witness i * star (D.witness 0)) = (D.projection 0).val
  rw [star_mul, star_star]
  calc
    _ = (D.witness 0 * (star (D.witness i) * D.witness i)) * star (D.witness 0) := by
      noncomm_ring
    _ = (D.projection 0).val := by rw [D.initial, V.mul_support, D.final]

private theorem rebased_final (i : ℕ) :
    D.rebasedPartial i * star (D.rebasedPartial i) = (D.projection i).val := by
  let V : PartialIsometry M := ⟨p, D.witness i, D.initial i⟩
  change (D.witness i * star (D.witness 0)) *
    star (D.witness i * star (D.witness 0)) = (D.projection i).val
  rw [star_mul, star_star]
  calc
    _ = (D.witness i * (star (D.witness 0) * D.witness 0)) * star (D.witness i) := by
      noncomm_ring
    _ = (D.projection i).val := by rw [D.initial, V.mul_support, D.final]

/-- The actual countable matrix units after rebasing to the first final projection. -/
def fullMatrixCorner : FullMatrixCorner (typeIIIInitialSpace (D.projection 0)) :=
  FullMatrixCorner.ofEquivalentProjectionFamily (typeIIIInitialSpace (D.projection 0))
    D.projection D.rebasedPartial D.rebased_initial D.rebased_final D.orthogonal
    (typeIIIInitialSpace_projection (D.projection 0)) D.total

theorem fullMatrixCorner_mem (i j : ℕ) : D.fullMatrixCorner.entry i j ∈ M :=
  FullMatrixCorner.ofEquivalentProjectionFamily_entry_mem _ D.projection D.rebasedPartial
    D.rebased_initial D.rebased_final D.orthogonal
    (typeIIIInitialSpace_projection (D.projection 0)) D.total i j

theorem first_nonzero (hp : p.val ≠ 0) : (D.projection 0).val ≠ 0 := by
  intro hz
  have hv : D.witness 0 = 0 :=
    (CStarRing.mul_star_self_eq_zero_iff _).mp ((D.final 0).trans hz)
  have hi := D.initial 0
  rw [hv, star_zero, zero_mul] at hi
  exact hp hi.symm

theorem first_finite (hfinite : FiniteProjectionIn M p.val) :
    FiniteProjectionIn M (D.projection 0).val :=
  finiteProjectionIn_of_equivalent p (D.projection 0) hfinite
    (D.witness 0) (D.initial 0) (D.final 0)

end CountableProjectionCopies

/-- A chosen finite nonzero full projection produces a finite full matrix corner. -/
theorem exists_finite_fullMatrixCorner_of_full_projection
    [TopologicalSpace.SeparableSpace H]
    (hPublished : PublishedProperInfiniteProjectionCopies.{u})
    (hInfinite : ProperlyInfiniteIdentity M) (p : AlgebraProjection M)
    (hfull : (centralSupport p).val = 1) (hp : p.val ≠ 0)
    (hfinite : FiniteProjectionIn M p.val) :
    ∃ q : AlgebraProjection M, q.val ≠ 0 ∧ FiniteProjectionIn M q.val ∧
      ∃ F : FullMatrixCorner (typeIIIInitialSpace q), ∀ i j, F.entry i j ∈ M := by
  obtain ⟨D⟩ := hPublished H M hInfinite p hfull
  exact ⟨D.projection 0, D.first_nonzero hp, D.first_finite hfinite,
    D.fullMatrixCorner, D.fullMatrixCorner_mem⟩

/-- In a factor, nonzeroness supplies the full-central-support hypothesis. -/
theorem exists_finite_fullMatrixCorner_of_factor
    [TopologicalSpace.SeparableSpace H]
    (hPublished : PublishedProperInfiniteProjectionCopies.{u})
    (hInfinite : ProperlyInfiniteIdentity M) (hfactor : ScalarCenter M)
    (p : AlgebraProjection M) (hp : p.val ≠ 0) (hfinite : FiniteProjectionIn M p.val) :
    ∃ q : AlgebraProjection M, q.val ≠ 0 ∧ FiniteProjectionIn M q.val ∧
      ∃ F : FullMatrixCorner (typeIIIInitialSpace q), ∀ i j, F.entry i j ∈ M := by
  apply exists_finite_fullMatrixCorner_of_full_projection hPublished hInfinite p ?_ hp hfinite
  apply centralSupport_eq_one_of_factor
  · intro c hc
    obtain ⟨z, hz⟩ := hfactor c.val c.property (fun a ha =>
      congrArg Subtype.val (hc ⟨a, ha⟩))
    exact ⟨z, Subtype.ext hz⟩
  · exact hp

end

end KadisonKastler

end OAI
