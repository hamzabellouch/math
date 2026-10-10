import OAI.Algebra.Finitistic.Bimodule.BimoduleDerivedFunctor
import OAI.Algebra.Finitistic.Rectification.InducedRectification

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u

/-- A finite interval of actual right-complex degrees, including both endpoints. -/
def intervalDegrees (lo hi : ℤ) (i : Fin ((hi-lo).toNat+1)) : ℤ := lo + i.val

theorem intervalDegrees_strictMono (lo hi : ℤ) : StrictMono (intervalDegrees lo hi) := by
  intro i j hij
  change lo + (i.val : ℤ) < lo + (j.val : ℤ)
  change i.val < j.val at hij
  omega

/-- Every degree in the support interval really occurs in the finite total. -/
theorem intervalDegrees_covers (lo hi n : ℤ) (hn : lo ≤ n ∧ n ≤ hi) :
    ∃ i, intervalDegrees lo hi i = n := by
  refine ⟨⟨(n-lo).toNat,by omega⟩,?_⟩
  dsimp [intervalDegrees]
  omega

variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]
variable (P : BiComplex k B)
variable [∀ n, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) n)]

/-- The native B-valued derived tensor total on a chosen support interval. -/
abbrev derivedInterval (lo hi : ℤ) :=
  derived k B P (intervalDegrees lo hi) (intervalDegrees_strictMono lo hi)

omit [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]
  [∀ n, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) n)] in
/-- Boundedness ensures this finite total contains every nonzero right degree. -/
theorem outside_interval_isZero (lo hi : ℤ)
    (hP : ∀ n, n < lo ∨ hi < n → IsZero (P.X n)) (n : ℤ)
    (hn : ∀ i, intervalDegrees lo hi i ≠ n) : IsZero (P.X n) := by
  apply hP n
  by_contra h
  have hbounds : lo ≤ n ∧ n ≤ hi := by omega
  obtain ⟨i,hi⟩ := intervalDegrees_covers lo hi n hbounds
  exact hn i hi
end LittleFinitistic.BimoduleTotal

end

end OAI
