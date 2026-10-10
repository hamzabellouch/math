import OAI.Analysis.BoundedHochschild.Conditional
import OAI.Analysis.BoundedHochschild.OperatorTransport

namespace OAI

/-!
# Vanishing for central partitions into proved cases

This is an unconditional application of the tracial argument and the full
operator algebra homotopy. Its structural hypothesis gives actual central
corners, each either faithfully normally tracial of type II₁ or explicitly
isomorphic to a full operator algebra. It makes no cohomological assumptions.
It does not assert that every von Neumann algebra has such a partition.
-/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners
open scoped ComplexOrder

universe u

/-- An actual presentation as a full algebra of Hilbert-space operators. -/
def FullOperatorAlgebra (N : Type u) [CStarAlgebra N] : Prop :=
  ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H), Nonempty ((H →L[ℂ] H) ≃⋆ₐ[ℂ] N)

theorem FullOperatorAlgebra.primitive {N : Type u} [CStarAlgebra N]
    (hN : FullOperatorAlgebra N) {n : ℕ} (f : Cochain N (n + 2))
    (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain N (n + 1), ‖g‖ ≤ ‖f‖ ∧
      ∀ x, differentialValue g x = f x := by
  rcases hN with ⟨H, hH, hHI, hHC, ⟨φ⟩⟩
  let := hH
  let := hHI
  let := hHC
  exact primitive_of_full_operator_equiv φ f hf

/-- A central partition into two classes for which the primitive is proved. -/
structure TracialOperatorPartition (M : Type u) [CStarAlgebra M]
    [PartialOrder M] [StarOrderedRing M] where
  Index : Type u
  projection : Index → M
  isProjection : ∀ i, IsStarProjection (projection i)
  central : ∀ i a, projection i * a = a * projection i
  orthogonal : ∀ i j, i ≠ j → projection i * projection j = 0
  total : ∀ x : M, (∀ i, projection i * x = 0) → x = 0
  cases : ∀ i, TracialTypeII (Corner (projection i) (isProjection i)) ∨
    FullOperatorAlgebra (Corner (projection i) (isProjection i))

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Uniform primitives assemble across an arbitrary, possibly uncountable center. -/
theorem primitive_of_tracial_operator_partition
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (D : TracialOperatorPartition M)
    {n : ℕ} (f : Cochain M (n + 2)) (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M (n + 1), ‖g‖ ≤ 12 * ‖f‖ + ((n + 1 : ℕ) : ℝ) * ‖f‖ ∧
      ∀ x, differentialValue g x = f x := by
  classical
  have hpieces (i : D.Index) :
      ∃ b : Cochain (Corner (D.projection i) (D.isProjection i)) (n + 1),
        ‖b‖ ≤ 12 * ‖f‖ ∧ ∀ x, differentialValue b x =
          CentralCorner.restrict (D.projection i) (D.isProjection i) (D.central i) f x := by
    let F := CentralCorner.restrict (D.projection i) (D.isProjection i) (D.central i) f
    have hF : ∀ x, differentialValue F x = 0 :=
      CentralCorner.restrict_cocycle _ _ _ f hf
    have hFn : ‖F‖ ≤ ‖f‖ := CentralCorner.restrict_norm _ _ _ f
    rcases D.cases i with htracial | hoperator
    · obtain ⟨b, hbn, hb⟩ := htracial.primitive F hF
      exact ⟨b, hbn.trans (mul_le_mul_of_nonneg_left hFn (by norm_num)), hb⟩
    · obtain ⟨b, hbn, hb⟩ := hoperator.primitive F hF
      refine ⟨b, (hbn.trans hFn).trans ?_, hb⟩
      nlinarith [norm_nonneg f]
  choose b hbn hb using hpieces
  exact primitive_of_central_cut_primitives e (HochschildSakai.mul_hasPreadjoint e)
    D.projection D.isProjection D.central D.orthogonal D.total f hf
    (fun i => CentralCorner.extend (D.projection i) (D.isProjection i) (D.central i) (b i))
    (fun i => CentralCorner.extend_supported _ _ _ _)
    (fun i => CentralCorner.extend_primitive _ _ _ f (b i) (hb i))
    (12 * ‖f‖) (by positivity)
    (fun i => (CentralCorner.extend_norm _ _ _ _).trans (hbn i))

/-- Actual-image cohomology vanishes under this structural, non-cohomological hypothesis. -/
theorem vanishing_of_tracial_operator_partition [WStarAlgebra M]
    (D : TracialOperatorPartition M) (k : ℕ) (hk : 2 ≤ k) :
    Subsingleton (Cohomology M k) := by
  apply (cohomology_subsingleton_iff M k).mpr
  obtain ⟨Y, hY, hYS, hYC, ⟨e⟩⟩ := WStarAlgebra.exists_predual (M := M)
  let := hY
  let := hYS
  let := hYC
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
  intro f hf
  obtain ⟨g, _, hg⟩ := primitive_of_tracial_operator_partition e D f
    ((differential_eq_zero_iff f).mp hf)
  refine ⟨g, ?_⟩
  ext x
  simpa only [incomingDifferential_succ, differential_apply] using hg x

end KadisonRingrose
end BoundedHochschild

end

end OAI
