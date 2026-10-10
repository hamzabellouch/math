import OAI.Analysis.BoundedHochschild.PublishedInputs
import OAI.Analysis.TracialCohomology.Vanishing

namespace OAI

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners
open scoped ComplexOrder

universe u

/-- The finite condition used in the von Neumann type decomposition. -/
def FiniteAlgebra (N : Type u) [CStarAlgebra N] : Prop :=
  ∀ v : N, star v * v = 1 → v * star v = 1

/-- There is no nonzero finite central corner with no type I central part. -/
def NoTypeII1Summand (N : Type u) [CStarAlgebra N]
    [PartialOrder N] [StarOrderedRing N] : Prop :=
  ∀ (z : N) (hz : IsStarProjection z), (∀ a : N, z * a = a * z) →
    FiniteAlgebra (Corner z hz) →
    PopaTypeII.NoTypeICentralPart (Corner z hz) → z = 0

/-- Precisely the trace data needed by the proved tracial primitive theorem. -/
def TracialTypeII (N : Type u) [CStarAlgebra N]
    [PartialOrder N] [StarOrderedRing N] : Prop :=
  ∃ (X : Type u) (_ : NormedAddCommGroup X) (_ : NormedSpace ℂ X)
    (_ : CompleteSpace X) (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N) (τ : N →ₚ[ℂ] ℂ),
    TraceInPredual e τ ∧ (∀ a b : N, τ (a * b) = τ (b * a)) ∧
    (∀ a : N, τ (star a * a) = 0 → a = 0) ∧ τ 1 = 1 ∧
    PopaTypeII.NoTypeICentralPart N

/-- The structural input supplies one exceptional corner and tracial II₁ corners. -/
structure CentralDecomposition (M : Type u) [CStarAlgebra M]
    [PartialOrder M] [StarOrderedRing M] where
  Index : Type u
  projection : Option Index → M
  isProjection : ∀ i, IsStarProjection (projection i)
  central : ∀ i a, projection i * a = a * projection i
  orthogonal : ∀ i j, i ≠ j → projection i * projection j = 0
  total : ∀ x : M, (∀ i, projection i * x = 0) → x = 0
  exceptional : NoTypeII1Summand (Corner (projection none) (isProjection none))
  tracial : ∀ i, TracialTypeII (Corner (projection (some i)) (isProjection (some i)))

/-- Blackadar's central type decomposition, specialized to the application. -/
def CentralDecompositionInput (M : Type u) [CStarAlgebra M]
    [PartialOrder M] [StarOrderedRing M] : Prop :=
  Nonempty (CentralDecomposition M)

def ClassicalVanishingInput : Prop :=
  ∀ (N : Type u) [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N],
    WStarAlgebra N → NoTypeII1Summand N →
    ∀ (n : ℕ) (f : Cochain N (n + 2)),
      (∀ x, differentialValue f x = 0) →
      ∃ g : Cochain N (n + 1), ∀ x, differentialValue g x = f x

theorem TracialTypeII.primitive {N : Type u} [CStarAlgebra N]
    [PartialOrder N] [StarOrderedRing N] (hN : TracialTypeII N)
    {n : ℕ} (f : Cochain N (n + 2)) (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain N (n + 1), ‖g‖ ≤ 12 * ‖f‖ ∧
      ∀ x, differentialValue g x = f x := by
  rcases hN with ⟨X, hX, hXS, hXC, e, τ, hτ, htr, hfaith, h1, hII⟩
  let := hX
  let := hXS
  let := hXC
  exact source_tracial_ordinary_primitive e τ hτ htr hfaith h1 hII f hf

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The manuscript's global assembly, conditional only on the two cited inputs. -/
theorem primitive_of_published_inputs (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hdecomp : CentralDecompositionInput M) (hclassical : ClassicalVanishingInput.{u})
    {n : ℕ} (f : Cochain M (n + 2)) (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M (n + 1), ∀ x, differentialValue g x = f x := by
  classical
  obtain ⟨D⟩ := hdecomp
  let p := D.projection
  let hp := D.isProjection
  let hc := D.central
  let e0 := cornerPredualEquiv (p none) (hp none) e
  let : WStarAlgebra (Corner (p none) (hp none)) :=
    ⟨⟨CornerPredual (p none) (hp none) e, inferInstance, inferInstance,
      inferInstance, ⟨e0⟩⟩⟩
  let f0 := CentralCorner.restrict (p none) (hp none) (hc none) f
  obtain ⟨b0, hb0⟩ := hclassical _ inferInstance D.exceptional n f0
    (CentralCorner.restrict_cocycle _ _ _ f hf)
  let C : ℝ := max ‖b0‖ (12 * ‖f‖)
  have hpieces (i : Option D.Index) :
      ∃ b : Cochain (Corner (p i) (hp i)) (n + 1), ‖b‖ ≤ C ∧
        ∀ x, differentialValue b x = CentralCorner.restrict (p i) (hp i) (hc i) f x := by
    cases i with
    | none => exact ⟨b0, le_max_left _ _, hb0⟩
    | some i =>
      obtain ⟨b, hbn, hb⟩ := (D.tracial i).primitive
        (CentralCorner.restrict (p (some i)) (hp (some i)) (hc (some i)) f)
        (CentralCorner.restrict_cocycle _ _ _ f hf)
      exact ⟨b, hbn.trans ((mul_le_mul_of_nonneg_left
        (CentralCorner.restrict_norm _ _ _ f) (by norm_num)).trans (le_max_right _ _)), hb⟩
  choose b hbn hb using hpieces
  obtain ⟨g, _, hg⟩ := primitive_of_central_cut_primitives e
    (HochschildSakai.mul_hasPreadjoint e) p hp hc D.orthogonal D.total f hf
    (fun i => CentralCorner.extend (p i) (hp i) (hc i) (b i))
    (fun i => CentralCorner.extend_supported _ _ _ _)
    (fun i => CentralCorner.extend_primitive _ _ _ f (b i) (hb i))
    C ((norm_nonneg b0).trans (le_max_left _ _))
    (fun i => (CentralCorner.extend_norm _ _ _ _).trans (hbn i))
  exact ⟨g, hg⟩

/-- Theorem 1.1, including vanishing of the actual-image cohomology quotient. -/
theorem vanishing_of_published_inputs [WStarAlgebra M]
    (hdecomp : CentralDecompositionInput M) (hclassical : ClassicalVanishingInput.{u})
    (k : ℕ) (hk : 2 ≤ k) :
    (∀ f : Cochain M k, differential f = 0 →
      ∃ g : Cochain M (k - 1), incomingDifferential M k g = f) ∧
    Subsingleton (Cohomology M k) := by
  have h : ∀ f : Cochain M k, differential f = 0 →
      ∃ g : Cochain M (k - 1), incomingDifferential M k g = f := by
    obtain ⟨Y, hY, hYS, hYC, ⟨e⟩⟩ := WStarAlgebra.exists_predual (M := M)
    let := hY
    let := hYS
    let := hYC
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
    intro f hf
    obtain ⟨g, hg⟩ := primitive_of_published_inputs e hdecomp hclassical f
      ((differential_eq_zero_iff f).mp hf)
    refine ⟨g, ?_⟩
    ext x
    simpa only [incomingDifferential_succ, differential_apply] using hg x
  exact ⟨h, (cohomology_subsingleton_iff M k).mpr h⟩

end KadisonRingrose
end BoundedHochschild

end

end OAI
