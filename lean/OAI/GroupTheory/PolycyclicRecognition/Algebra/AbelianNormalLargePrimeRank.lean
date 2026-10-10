import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianNormalFiniteRank
import OAI.GroupTheory.PolycyclicRecognition.Algebra.UniformMonoidAlgebraGenerators
import Mathlib.Data.Nat.Factorial.NatCast
import Mathlib.Algebra.Field.ZMod
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteIntegralTorsion
import Mathlib.RingTheory.Finiteness.Cardinality

namespace OAI

/-! # Finite prime reductions outside a fixed finite set

The same integer group generators bound the necessary exterior degree for
all coefficient fields. When the characteristic exceeds that degree, the
factorial comparison in actual homology is invertible.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra TensorProduct IsMulCommutative
variable {G : Type} [Group G] [Group.FG G]
  (N : Subgroup G) [N.Normal] [IsMulCommutative N] [IsMulCommutative (G ⧸ N)]

theorem abelian_normal_large_prime_scalar_rank (h : TypeFPInfinity G) :
    ∃ b : ℕ, ∀ p : ℕ, (hp : p.Prime) → b < p →
      let : Fact p.Prime := ⟨hp⟩
      FiniteDimensional (ZMod p) (ZMod p ⊗[ℤ] Additive N) := by
  obtain ⟨s, hs⟩ := (Monoid.FG.fg_top : (⊤ : Submonoid (G ⧸ N)).FG)
  let r := Fintype.card s
  refine ⟨r + 1, fun p hp hlarge => ?_⟩
  let : Fact p.Prime := ⟨hp⟩
  let K := ZMod p
  let ρ := scalarExtendedRepresentation K (abelianKernelQuotientConjugationAction N)
  let := abelianKernelQuotient_finite N
  let : Module.Finite K[G ⧸ N] ρ.asModule :=
    scalarExtendedRepresentation_finite K (abelianKernelQuotientConjugationAction N)
  obtain ⟨a, ha⟩ := monoidAlgebra_generators_of_closure s hs K
  have hfact : ((r + 1).factorial : K) ≠ 0 := by
    exact ((IsUnit.natCast_factorial_iff_of_charP (A := K) p).mpr hlarge).ne_zero
  let : Module.Finite K[G ⧸ N] (higherExteriorRepresentation ρ (r + 1)).asModule :=
    typeFPInfinity_abelianNormalHigherExterior_finite_of_factorial_ne_zero K N h r hfact
  apply finite_representation_of_no_free_orbit ρ
  intro g v hv
  have hc : Function.Injective (fun i : Fin (r + 1 + 1) => (i.val : K)) := by
    intro i j hij
    apply Fin.ext
    have hi : i.val < p := lt_of_lt_of_le i.isLt (by omega)
    have hj : j.val < p := lt_of_lt_of_le j.isLt (by omega)
    have hh := congrArg ZMod.val hij
    simpa only [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] using hh
  have hb := higherExterior_free_orbit_bound ρ a ha
    (fun i : Fin (r + 1 + 1) => (i.val : K)) hc g v hv
  omega

theorem abelian_normal_large_prime_reduction_finite (h : TypeFPInfinity G) :
    ∃ b : ℕ, ∀ p : ℕ, p.Prime → b < p →
      Finite (Additive N ⧸ integerMultiples (Additive N) p) := by
  obtain ⟨b, hb⟩ := abelian_normal_large_prime_scalar_rank N h
  refine ⟨b, fun p hp hlarge => ?_⟩
  let : Fact p.Prime := ⟨hp⟩
  let := hb p hp hlarge
  let : Finite (ZMod p ⊗[ℤ] Additive N) := Module.finite_of_finite (ZMod p)
  exact Finite.of_equiv _ (integerReductionEquiv (Additive N) p).toEquiv

end PolycyclicRecognition

end

end OAI
