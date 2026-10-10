import OAI.GroupTheory.PolycyclicRecognition.Finiteness.AbelianSecondHomologyPairing
import Mathlib.GroupTheory.Commutator.Basic

namespace OAI

/-! # The exact bar-boundary correction for a commutator

The antisymmetric two-letter chain is a cycle only for commuting letters.
The correction below measures its failure in the actual group bar complex.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

def commutatorBarChain (a b : G) : (G × G) →₀ ℤ :=
  Finsupp.single (a, b) 1 - Finsupp.single (b, a) 1

theorem commutatorBarChain_boundary (a b : G) :
    groupHomology.d₂₁ (integralTrivialCoefficient G) (commutatorBarChain a b) =
      Finsupp.single (b * a) 1 - Finsupp.single (a * b) 1 := by
  change groupHomology.d₂₁ (integralTrivialCoefficient G)
    (Finsupp.single (a, b) 1 - Finsupp.single (b, a) 1) = _
  rw [map_sub, groupHomology.d₂₁_single, groupHomology.d₂₁_single]
  change Finsupp.single b 1 - Finsupp.single (a * b) 1 + Finsupp.single a 1 -
    (Finsupp.single a 1 - Finsupp.single (b * a) 1 + Finsupp.single b 1) = _
  abel

def commutatorBarPrimitive (a b : G) : (G × G) →₀ ℤ :=
  Finsupp.single (⁅a, b⁆, b * a) 1 - commutatorBarChain a b

theorem commutatorBarPrimitive_boundary (a b : G) :
    groupHomology.d₂₁ (integralTrivialCoefficient G) (commutatorBarPrimitive a b) =
      Finsupp.single ⁅a, b⁆ 1 := by
  change groupHomology.d₂₁ (integralTrivialCoefficient G)
    (Finsupp.single (⁅a, b⁆, b * a) 1 - commutatorBarChain a b) = _
  rw [map_sub, groupHomology.d₂₁_single, commutatorBarChain_boundary]
  change Finsupp.single (b * a) 1 - Finsupp.single (⁅a, b⁆ * (b * a)) 1 +
    Finsupp.single ⁅a, b⁆ 1 -
      (Finsupp.single (b * a) 1 - Finsupp.single (a * b) 1) = _
  have he : ⁅a, b⁆ * (b * a) = a * b := by simp [commutatorElement_def, mul_assoc]
  rw [he]
  abel

theorem commutatorBarChain_cycle_iff (a b : G) :
    groupHomology.d₂₁ (integralTrivialCoefficient G) (commutatorBarChain a b) = 0 ↔
      Commute a b := by
  classical
  rw [commutatorBarChain_boundary, sub_eq_zero]
  constructor
  · intro he
    have h := congrArg (fun c : G →₀ ℤ => c (a * b)) he
    by_contra hn
    have hne : b * a ≠ a * b := fun e => hn e.symm
    rw [Finsupp.single_eq_of_ne hne.symm, Finsupp.single_eq_same] at h
    exact zero_ne_one h
  · intro h
    rw [h.eq]

end PolycyclicRecognition

end

end OAI
