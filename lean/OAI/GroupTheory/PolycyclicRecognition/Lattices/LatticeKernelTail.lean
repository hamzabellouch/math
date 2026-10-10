import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FreeAbelianDuality

namespace OAI

/-! # Removing the first coordinate of a free abelian quotient -/

noncomputable section
namespace PolycyclicRecognition

def latticeTail (n : ℕ) : IntegralLatticeGroup (n + 1) →* IntegralLatticeGroup n where
  toFun a := Multiplicative.ofAdd (fun i => a.toAdd i.succ)
  map_one' := rfl
  map_mul' _ _ := rfl

variable {G : Type} [Group G] {n : ℕ} (q : G →* IntegralLatticeGroup (n + 1))

def latticeKernelTail : ( (latticeCoordinate n).comp q).ker →* IntegralLatticeGroup n :=
  (latticeTail n).comp (q.comp ((latticeCoordinate n).comp q).ker.subtype)

theorem latticeKernelTail_surjective (hq : Function.Surjective q) :
    Function.Surjective (latticeKernelTail q) := by
  intro a
  obtain ⟨g, hg⟩ := hq (Multiplicative.ofAdd (Fin.cases 0 a.toAdd))
  have hg0 : g ∈ ((latticeCoordinate n).comp q).ker := by
    change latticeCoordinate n (q g) = 1
    rw [hg]
    rfl
  refine ⟨⟨g, hg0⟩, ?_⟩
  change latticeTail n (q g) = a
  rw [hg]
  rfl

def latticeKernelTailEquiv : q.ker ≃* (latticeKernelTail q).ker where
  toFun a := ⟨⟨a, by
    change latticeCoordinate n (q a) = 1
    rw [a.property, map_one]⟩, by
    change latticeTail n (q a) = 1
    rw [a.property, map_one]⟩
  invFun a := ⟨a.val.val, by
    apply Multiplicative.toAdd.injective
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact congrArg Multiplicative.toAdd a.val.property
    · exact congrFun (congrArg Multiplicative.toAdd a.property) j⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end PolycyclicRecognition

end

end OAI
