import OAI.Analysis.KadisonKastler.AbelianCyclicCommutant
import OAI.Analysis.KadisonKastler.AbelianInvariantMean
import OAI.Analysis.KadisonKastler.FixedPointGap
import OAI.Analysis.KadisonKastler.Amenable
import Mathlib.Analysis.CStarAlgebra.Unitary.Span

namespace OAI

/-! # A contractive expectation for a cyclic commutative algebra

Average the conjugation action of the discrete abelian unitary group.
Its fixed operators lie in the commutant, which is the original algebra
by cyclicity. No normality of the expectation is asserted or needed.
-/

namespace KadisonKastler

open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem mem_commutant_of_commute_unitaries (M : VonNeumannAlgebra H)
    (T : H →L[ℂ] H)
    (hT : ∀ u : unitary (Algebra M), Commute (u : H →L[ℂ] H) T) :
    T ∈ M.commutant := by
  let : CStarAlgebra (Algebra M) := {}
  let D : Algebra M →ₗ[ℂ] (H →L[ℂ] H) :=
    ((LinearMap.mulLeft ℂ T) - (LinearMap.mulRight ℂ T)).comp
      M.toStarSubalgebra.subtype.toAlgHom.toLinearMap
  have hspan : Submodule.span ℂ (unitary (Algebra M) : Set (Algebra M)) ≤ D.ker := by
    apply Submodule.span_le.mpr
    intro a ha
    change T * a.val - a.val * T = 0
    exact sub_eq_zero.mpr (hT ⟨a, ha⟩).eq.symm
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro a ha
  have hmem : (⟨a, ha⟩ : Algebra M) ∈
      Submodule.span ℂ (unitary (Algebra M) : Set (Algebra M)) := by
    rw [CStarAlgebra.span_unitary]
    trivial
  exact (sub_eq_zero.mp (hspan hmem)).symm

theorem isInjective_of_commutative_cyclic (M : VonNeumannAlgebra H) (ξ : H)
    (hcomm : ∀ a b : Algebra M, a * b = b * a)
    (hcyclic : DenseRange (fun a : Algebra M => a.val ξ)) : IsInjective M := by
  let : CommRing (Algebra M) := { (inferInstance : Ring (Algebra M)) with
    mul_comm := hcomm }
  let G := unitary (Algebra M)
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := ⟨rfl⟩
  let U : G →* unitary (H →L[ℂ] H) :=
    (Unitary.map (StarMonoidHom.ofClass M.toStarSubalgebra.subtype)).toMonoidHom
  let m := abelianScalarInvariantMean G
  let F := m.averageConjugation U
  let E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) := F.toLinearMap.mkContinuous 1
    (fun T => by
      change ‖m.averageConjugation U T‖ ≤ 1 * ‖T‖
      simpa only [one_mul] using m.averageConjugation_norm_le U T)
  refine ⟨E, E.opNorm_le_bound zero_le_one (fun T => by
    change ‖m.averageConjugation U T‖ ≤ 1 * ‖T‖
    simpa only [one_mul] using m.averageConjugation_norm_le U T), ?_, ?_⟩
  · intro T
    apply mem_of_mem_commutant_of_cyclic_commutative M ξ hcomm hcyclic
    apply mem_commutant_of_commute_unitaries M
    intro u
    have h := m.averageConjugation_invariant U T u
    have he := congrArg (fun S : H →L[ℂ] H => S * (U u : H →L[ℂ] H)) h
    change ((U u : H →L[ℂ] H) * E T * star (U u : H →L[ℂ] H)) * U u = E T * U u at he
    simp only [mul_assoc, (U u).property.1, mul_one] at he
    exact he
  · intro T hT
    apply m.averageConjugation_eq_of_commutes U T
    intro u
    change Commute T ((u : Algebra M).val)
    exact congrArg Subtype.val (hcomm ⟨T, hT⟩ u.val)

end

end KadisonKastler

end OAI
