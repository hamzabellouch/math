import OAI.GroupTheory.PolycyclicRecognition.Algebra.CocycleGrowth
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OAI

/-!
# The precise published reduced-cohomology input

Cornulier--Tessera, *On the vanishing of reduced 1-cohomology for Banach
representations*, Ann. Inst. Fourier 70 (2020), 1951--2003, Corollary 1.9,
together with Definition 1.1: real-triangulable Lie groups have `WAP_t`.
The proposition below is only its real Hilbert-space consequence, for the
particular representation used by the application. Isometric Hilbert
representations are weakly almost periodic. The topology on cocycles is
uniform norm convergence on compact subsets, as defined in §1.1.

Source: https://aif.centre-mersenne.org/item/10.5802/aif.3363.pdf
-/

namespace PolycyclicRecognition

variable (G E : Type*) [Group G] [TopologicalSpace G]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [DistribMulAction G E] [IsIsometricSMul G E] [SMulCommClass G ℝ E]

/-- The needed Hilbert-space specialization of Corollary 1.9. Continuity and
absence of invariant vectors are hypotheses of the published theorem. -/
def ReducedCohomologyInput (G E : Type*) [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [DistribMulAction G E] [IsIsometricSMul G E] [SMulCommClass G ℝ E] : Prop :=
  (∀ v : E, (∀ g : G, g • v = v) → v = 0) →
  (∀ v : E, Continuous (fun g : G => g • v)) →
  ∀ b : G → E, Continuous b → IsCocycle b →
    ∀ Q : Set G, IsCompact Q → ∀ ε : ℝ, 0 < ε →
      ∃ φ : E, ∀ q ∈ Q, ‖b q + q • φ - φ‖ ≤ ε

/-- The published input has the required quantitative consequence for the
actual word-length estimate. The approximation vector is chosen before the
word length tends to infinity. -/
theorem sublinear_of_reducedCohomologyInput
    (hvan : ReducedCohomologyInput G E)
    (hfixed : ∀ v : E, (∀ g : G, g • v = v) → v = 0)
    (hact : ∀ v : E, Continuous (fun g : G => g • v))
    (b : G → E) (hbcont : Continuous b) (hb : IsCocycle b)
    (Q : Set G) (hQ : IsCompact Q) (length : G → ℝ)
    (hlen : ∀ g, 0 ≤ length g) {a : ℝ} (ha : 0 ≤ a)
    (hword : ∀ g, ∃ l : List G, (∀ q ∈ l, q ∈ Q) ∧ l.prod = g ∧
      (l.length : ℝ) ≤ a * length g + a) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g, ‖b g‖ ≤ ε * length g + B := by
  exact hb.sublinear_of_coboundary_approximation Q length hlen ha hword
    (hvan hfixed hact b hbcont hb Q hQ)

end PolycyclicRecognition

end OAI
