import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicPowerIndex
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CharacteristicFiniteIndex

namespace OAI

/-! # Restricting a cyclic extension to a characteristic finite-index base -/

noncomputable section
namespace PolycyclicRecognition
variable {H : Type} [Group H] (K : Subgroup H) [K.Characteristic] (a : MulAut H)

def characteristicCyclicMap :
    (K ⋊[integerPowerAction (MulAut.characteristic K a)] Multiplicative ℤ) →*
      (H ⋊[integerPowerAction a] Multiplicative ℤ) :=
  SemidirectProduct.map K.subtype (MonoidHom.id _) (by
    intro n
    ext x
    change (((MulAut.characteristic K a) ^ n.toAdd) x : H) = (a ^ n.toAdd) (x : H)
    rw [← map_zpow]
    rfl)

theorem characteristicCyclicMap_injective : Function.Injective (characteristicCyclicMap K a) := by
  intro x y h
  apply SemidirectProduct.ext
  · apply Subtype.ext
    exact congrArg (fun z : H ⋊[integerPowerAction a] Multiplicative ℤ => z.left) h
  · exact congrArg (fun z : H ⋊[integerPowerAction a] Multiplicative ℤ => z.right) h

theorem mem_characteristicCyclicMap_range (g : H ⋊[integerPowerAction a] Multiplicative ℤ) :
    g ∈ (characteristicCyclicMap K a).range ↔ g.left ∈ K := by
  constructor
  · rintro ⟨x, rfl⟩
    exact x.left.property
  · intro hg
    exact ⟨⟨⟨g.left, hg⟩, g.right⟩, rfl⟩

theorem characteristicCyclicMap_finiteIndex [K.FiniteIndex] :
    (characteristicCyclicMap K a).range.FiniteIndex := by
  let G := H ⋊[integerPowerAction a] Multiplicative ℤ
  let R := (characteristicCyclicMap K a).range
  let f : H ⧸ K → G ⧸ R := Quotient.map' (fun h : H => (SemidirectProduct.inl h : G)) (by
    intro x y hxy
    rw [QuotientGroup.leftRel_apply] at hxy ⊢
    rw [mem_characteristicCyclicMap_range]
    simpa only [← map_inv, ← map_mul, SemidirectProduct.left_inl] using hxy)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨g, rfl⟩ := Quotient.mk''_surjective q
    refine ⟨QuotientGroup.mk g.left, ?_⟩
    change QuotientGroup.mk (SemidirectProduct.inl g.left : G) = QuotientGroup.mk g
    apply QuotientGroup.eq.mpr
    rw [mem_characteristicCyclicMap_range]
    simp
  let : Finite (G ⧸ R) := Finite.of_surjective f hf
  exact Subgroup.finiteIndex_of_finite_quotient

end PolycyclicRecognition

end

end OAI
