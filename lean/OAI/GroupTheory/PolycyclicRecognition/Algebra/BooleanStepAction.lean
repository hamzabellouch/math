import OAI.GroupTheory.PolycyclicRecognition.Finiteness.BooleanStepProjective

namespace OAI

/-! # Translation on a Boolean step-function ring -/
noncomputable section
namespace PolycyclicRecognition
variable {G I : Type} [Group G]
variable (a : I → G → Bool) (t : G → I → I)
variable (ht : ∀ g i x, a i (g⁻¹ * x) = a (t g i) x)

def booleanStepTranslate (g : G) (f : booleanStepRing a) : booleanStepRing a := by
  classical
  refine ⟨fun x => f.val (g⁻¹ * x), ?_⟩
  obtain ⟨s, hs⟩ := f.property
  refine ⟨s.image (t g), fun x y hxy => hs _ _ ?_⟩
  intro i hi
  rw [ht, ht]
  exact hxy (t g i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

/-- The action is by actual ring automorphisms, given by left translation. -/
@[instance_reducible]
def booleanStepMulSemiringAction : MulSemiringAction G (booleanStepRing a) where
  smul := booleanStepTranslate a t ht
  one_smul f := by
    apply Subtype.ext
    funext x
    change f.val (1⁻¹ * x) = f.val x
    rw [inv_one, one_mul]
  mul_smul g h f := by
    apply Subtype.ext
    funext x
    change f.val ((g * h)⁻¹ * x) = f.val (h⁻¹ * (g⁻¹ * x))
    rw [mul_inv_rev, mul_assoc]
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

@[simp]
theorem booleanStepTranslate_apply (g : G) (f : booleanStepRing a) (x : G) :
    (booleanStepTranslate a t ht g f).val x = f.val (g⁻¹ * x) := rfl

end PolycyclicRecognition

end

end OAI
