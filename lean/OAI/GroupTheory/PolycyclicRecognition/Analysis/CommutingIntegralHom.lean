import OAI.GroupTheory.PolycyclicRecognition.Lattices.IntegralLatticeGenerators
import Mathlib.GroupTheory.Subgroup.Centralizer

namespace OAI

/-! # The homomorphism determined by commuting integral generators -/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {H : Type} [Group H] {n : ℕ}

def commutingIntegralHom (a : Fin n → H) (ha : ∀ i j, Commute (a i) (a j)) :
    IntegralLatticeGroup n →* H := by
  classical
  let K := Subgroup.closure (Set.range a)
  have hc : (Set.range a).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact ha i j
  letI : IsMulCommutative K := Subgroup.isMulCommutative_closure hc
  let b : Fin n → K := fun i => ⟨a i, Subgroup.subset_closure (Set.mem_range_self i)⟩
  let f : IntegralLatticeGroup n →* K :=
    { toFun := fun z => ∏ i, b i ^ z.toAdd i
      map_one' := by simp
      map_mul' := by
        intro z w
        change (∏ i, b i ^ (z.toAdd i + w.toAdd i)) = _
        simp only [zpow_add, Finset.prod_mul_distrib] }
  exact K.subtype.comp f

@[simp] theorem commutingIntegralHom_generator
    (a : Fin n → H) (ha : ∀ i j, Commute (a i) (a j)) (j : Fin n) :
    commutingIntegralHom a ha (integralLatticeGenerator n j) = a j := by
  classical
  unfold commutingIntegralHom
  simp only [MonoidHom.comp_apply, integralLatticeGenerator,
    Pi.basisFun_apply]
  simp [Pi.single_apply]

theorem commutingIntegralHom_range_le (a : Fin n → H)
    (ha : ∀ i j, Commute (a i) (a j)) (K : Subgroup H) (hk : ∀ i, a i ∈ K) :
    (commutingIntegralHom a ha).range ≤ K := by
  have ht : (⊤ : Subgroup (IntegralLatticeGroup n)) ≤
      K.comap (commutingIntegralHom a ha) := by
    rw [← integralLatticeGenerator_closure n]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    change commutingIntegralHom a ha (integralLatticeGenerator n i) ∈ K
    rw [commutingIntegralHom_generator]
    exact hk i
  rintro _ ⟨z, rfl⟩
  exact ht (Subgroup.mem_top z)

end PolycyclicRecognition

end

end OAI
