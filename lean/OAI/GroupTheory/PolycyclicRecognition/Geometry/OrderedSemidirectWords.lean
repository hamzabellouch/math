import OAI.GroupTheory.PolycyclicRecognition.Lattices.IntegerSemidirectLattice
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialModelWords

namespace OAI

/-! # Ordered integral words in an infinite cyclic extension -/

namespace PolycyclicRecognition
variable {H G : Type*} [Group H] [Group G] {d : ℕ}

theorem orderedWord_snoc (X : Fin d → G) (t : G) (z : Fin (d + 1) → ℤ) :
    orderedWord (Fin.snoc X t) z =
      orderedWord X (fun i => z i.castSucc) * t ^ z (Fin.last d) := by
  simp only [orderedWord, List.ofFn_succ', List.prod_concat, Fin.snoc_castSucc, Fin.snoc_last]

def cyclicExtensionGenerators (a : MulAut H) (X : Fin d → H) :
    Fin (d + 1) → H ⋊[integerPowerAction a] Multiplicative ℤ :=
  Fin.snoc (fun i => SemidirectProduct.inl (X i))
    (SemidirectProduct.inr (Multiplicative.ofAdd 1))

theorem cyclicExtension_orderedWord (a : MulAut H) (X : Fin d → H)
    (z : Fin (d + 1) → ℤ) :
    orderedWord (cyclicExtensionGenerators a X) z =
      SemidirectProduct.inl (orderedWord X (fun i => z i.castSucc)) *
        SemidirectProduct.inr (Multiplicative.ofAdd (z (Fin.last d))) := by
  rw [cyclicExtensionGenerators, orderedWord_snoc, orderedWord_map, ← map_zpow]
  congr 2
  change (z (Fin.last d)) • (1 : ℤ) = z (Fin.last d)
  simp

theorem cyclicExtension_orderedWord_surjective (a : MulAut H) (X : Fin d → H)
    (hX : Function.Surjective (orderedWord X)) :
    Function.Surjective (orderedWord (cyclicExtensionGenerators a X)) := by
  intro g
  obtain ⟨z, hz⟩ := hX g.left
  refine ⟨Fin.snoc z g.right.toAdd, ?_⟩
  rw [cyclicExtension_orderedWord]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, hz, ofAdd_toAdd]
  exact SemidirectProduct.inl_left_mul_inr_right g

theorem cyclicExtension_orderedWord_injective (a : MulAut H) (X : Fin d → H)
    (hX : Function.Injective (orderedWord X)) :
    Function.Injective (orderedWord (cyclicExtensionGenerators a X)) := by
  intro z w h
  rw [cyclicExtension_orderedWord, cyclicExtension_orderedWord] at h
  have hl : (fun i : Fin d => z i.castSucc) = (fun i => w i.castSucc) := by
    apply hX
    simpa using congrArg SemidirectProduct.left h
  have hr : z (Fin.last d) = w (Fin.last d) := by
    simpa using congrArg
      (fun g : H ⋊[integerPowerAction a] Multiplicative ℤ => g.right.toAdd) h
  funext i
  exact Fin.lastCases hr (fun i => congrFun hl i) i

end PolycyclicRecognition

end OAI
