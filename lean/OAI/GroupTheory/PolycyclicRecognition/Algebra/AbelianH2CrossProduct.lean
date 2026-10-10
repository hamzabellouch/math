import OAI.GroupTheory.PolycyclicRecognition.Finiteness.AbelianSecondHomologyPairing

namespace OAI

/-! # The alternating cross product in second homology of an abelian group -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {A : Type} [CommGroup A]

def abelianH2Class (a b : A) : groupHomology.H2 (integralTrivialCoefficient A) :=
  groupHomology.H2π (integralTrivialCoefficient A) (antisymmetricBarCycle a b)

@[simp] theorem abelianH2Class_self (a : A) : abelianH2Class a a = 0 := by
  change groupHomology.H2π (integralTrivialCoefficient A) _ = 0
  have h : antisymmetricBarCycle a a = 0 := by
    apply Subtype.ext
    simp [antisymmetricBarCycle]
  rw [h, map_zero]

theorem abelianH2Class_swap (a b : A) : abelianH2Class b a = -abelianH2Class a b := by
  have h : antisymmetricBarCycle b a = -antisymmetricBarCycle a b := by
    apply Subtype.ext
    change Finsupp.single (b, a) 1 - Finsupp.single (a, b) 1 =
      -(Finsupp.single (a, b) 1 - Finsupp.single (b, a) 1)
    abel
  change groupHomology.H2π (integralTrivialCoefficient A) _ = _
  rw [h, map_neg]
  rfl

theorem abelianH2Class_mul_left (a b c : A) :
    abelianH2Class (a * b) c = abelianH2Class a c + abelianH2Class b c := by
  change groupHomology.H2π (integralTrivialCoefficient A) _ =
    groupHomology.H2π (integralTrivialCoefficient A) _ +
      groupHomology.H2π (integralTrivialCoefficient A) _
  rw [← map_add, groupHomology.H2π_eq_iff]
  refine ⟨-(Finsupp.single (a, b, c) 1 - Finsupp.single (a, c, b) 1 +
    Finsupp.single (c, a, b) 1), ?_⟩
  rw [map_neg, map_add, map_sub, groupHomology.d₃₂_single,
    groupHomology.d₃₂_single, groupHomology.d₃₂_single]
  change -((Finsupp.single (b, c) 1 - Finsupp.single (a * b, c) 1 +
      Finsupp.single (a, b * c) 1 - Finsupp.single (a, b) 1) -
    (Finsupp.single (c, b) 1 - Finsupp.single (a * c, b) 1 +
      Finsupp.single (a, c * b) 1 - Finsupp.single (a, c) 1) +
    (Finsupp.single (a, b) 1 - Finsupp.single (c * a, b) 1 +
      Finsupp.single (c, a * b) 1 - Finsupp.single (c, a) 1)) =
    (Finsupp.single (a * b, c) 1 - Finsupp.single (c, a * b) 1) -
      ((Finsupp.single (a, c) 1 - Finsupp.single (c, a) 1) +
        (Finsupp.single (b, c) 1 - Finsupp.single (c, b) 1))
  rw [mul_comm c a, mul_comm c b]
  abel

theorem abelianH2Class_mul_right (a b c : A) :
    abelianH2Class a (b * c) = abelianH2Class a b + abelianH2Class a c := by
  rw [abelianH2Class_swap, abelianH2Class_mul_left,
    abelianH2Class_swap b a, abelianH2Class_swap c a]
  abel

@[simp] theorem abelianH2Class_one_left (a : A) : abelianH2Class 1 a = 0 := by
  have h := abelianH2Class_mul_left (1 : A) 1 a
  have hz : abelianH2Class 1 a + 0 = abelianH2Class 1 a + abelianH2Class 1 a := by
    simpa only [one_mul, add_zero] using h
  exact (add_left_cancel hz).symm

@[simp] theorem abelianH2Class_one_right (a : A) : abelianH2Class a 1 = 0 := by
  rw [abelianH2Class_swap, abelianH2Class_one_left, neg_zero]

def abelianH2Pairing : Additive A →+ Additive A →+
    groupHomology.H2 (integralTrivialCoefficient A) where
  toFun a :=
    { toFun b := abelianH2Class a.toMul b.toMul
      map_zero' := abelianH2Class_one_right a.toMul
      map_add' b c := abelianH2Class_mul_right a.toMul b.toMul c.toMul }
  map_zero' := by
    apply AddMonoidHom.ext
    intro a
    exact abelianH2Class_one_left a.toMul
  map_add' a b := by
    apply AddMonoidHom.ext
    intro c
    exact abelianH2Class_mul_left a.toMul b.toMul c.toMul

end PolycyclicRecognition

end

end OAI
