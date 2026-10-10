import OAI.Analysis.KadisonKastler.Algebra
import OAI.Analysis.KadisonKastler.PublishedCentralDecomposition
import OAI.Analysis.KadisonKastler.PositiveCompressionFullness

namespace OAI

/-! # The two projection inputs needed for type III compression

Blackadar, *Operator Algebras* (2006), I.6.1.2--5 and I.9.2.1(iv),
give a nonzero spectral projection above any positive threshold below
the norm of a positive element. III.1.3.5--7 and III.1.4.2 give equivalence
of every nonzero projection to the identity in a countably decomposable
type III factor. Only these projection statements are assumed below.
Neither input asserts simplicity of an ultraproduct or a perturbation bound.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance typeIIIAlgebraLE (M : VonNeumannAlgebra H) : LE (Algebra M) :=
  (CStarAlgebra.spectralOrder (Algebra M)).toLE
local instance typeIIIAlgebraOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance typeIIIAlgebraStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

/-- Finiteness of a projection: an isometry with initial projection `p`
and range under `p` has range exactly `p`. -/
def FiniteProjectionIn (M : VonNeumannAlgebra H) (p : Algebra M) : Prop :=
  ∀ v : Algebra M, star v * v = p → p * v = v → v * star v = p

/-- The ordinary nonzero type III factor conditions, with type III
expressed as absence of nonzero finite projections. -/
structure TypeIIIFactor (M : VonNeumannAlgebra H) : Prop where
  nonzero : (1 : H →L[ℂ] H) ≠ 0
  factor : ScalarCenter M
  purelyInfinite : ∀ p : Algebra M, IsStarProjection p → FiniteProjectionIn M p → p = 0

def PublishedVonNeumannSpectralCut : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    ∀ (M : VonNeumannAlgebra H) (x : Algebra M) (t : ℝ),
      0 < t → t < ‖star x * x‖ →
      ∃ p : Algebra M, IsStarProjection p ∧ p ≠ 0 ∧
        t • p ≤ star x * x

def PublishedTypeIIIProjectionComparison : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H],
    ∀ (M : VonNeumannAlgebra H), TypeIIIFactor M →
      ∀ p : Algebra M, IsStarProjection p → p ≠ 0 →
        ∃ v : Algebra M, star v * v = 1 ∧ v * star v = p

theorem typeIII_positive_compression
    [TopologicalSpace.SeparableSpace H]
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (M : VonNeumannAlgebra H) (hM : TypeIIIFactor M)
    (x : Algebra M) {ε : ℝ} (hε : 0 < ε) (hx : ε ≤ ‖x‖) :
    ∃ v : Algebra M, star v * v = 1 ∧
      algebraMap ℝ (Algebra M) (ε ^ 2 / 2) ≤ star v * (star x * x) * v := by
  have ht : 0 < ε ^ 2 / 2 := by positivity
  have hlt : ε ^ 2 / 2 < ‖star x * x‖ := by
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg x]
  obtain ⟨p, hp, hpne, hpx⟩ := hSpectral H M x (ε ^ 2 / 2) ht hlt
  obtain ⟨v, hv, hvp⟩ := hCompare H M hM p hp hpne
  refine ⟨v, hv, ?_⟩
  have h := star_left_conjugate_le_conjugate hpx v
  have hvpv : star v * p * v = 1 := by
    rw [← hvp]
    calc
      star v * (v * star v) * v = (star v * v) * (star v * v) := by simp [mul_assoc]
      _ = 1 := by rw [hv, one_mul]
  simpa only [mul_smul_comm, smul_mul_assoc, hvpv, Algebra.algebraMap_eq_smul_one] using h

end

end KadisonKastler

end OAI
