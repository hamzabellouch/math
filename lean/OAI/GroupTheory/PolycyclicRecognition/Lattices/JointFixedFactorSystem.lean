import OAI.GroupTheory.PolycyclicRecognition.Lattices.JointFixedSubalgebra
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorExtensionMap
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GroupExtensionFactorSystem

namespace OAI

/-! # The actual extension on the joint fixed kernel

Once the section factors are fixed by the family, the joint fixed subgroup
supports the same nonabelian cocycle. Its factor extension embeds faithfully
in the original group.
-/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] polynomialSubalgebraGroup
variable {L Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group Q]

def jointFixedFactorSystem (F : NonabelianFactorSystem L Q)
    (A : Q → L ≃ₗ⁅ℝ⁆ L) (hact : ∀ q x, F.action q x = A q x)
    (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (hcomm : ∀ S ∈ ss, ∀ q, Commute S.toLinearMap (A q).toLinearMap)
    (hfixed : ∀ S ∈ ss, ∀ q r, S (F.factor q r) = F.factor q r) :
    NonabelianFactorSystem (jointFixedLieSubalgebra ss) Q where
  action q := jointFixedGroupAction ss (A q) (fun S hS => hcomm S hS q)
  factor q r := ⟨F.factor q r, (mem_jointFixedLieSubalgebra ss _).mpr
    (fun S hS => hfixed S hS q r)⟩
  action_one := by
    apply DFunLike.ext
    intro x
    apply Subtype.ext
    change A 1 x = x
    rw [← hact, F.action_one]
    rfl
  factor_one_left q := Subtype.ext (F.factor_one_left q)
  factor_one_right q := Subtype.ext (F.factor_one_right q)
  action_mul q r := by
    apply DFunLike.ext
    intro x
    apply Subtype.ext
    change A q (A r x) = F.factor q r * A (q * r) x * (F.factor q r)⁻¹
    rw [← hact, ← hact, ← hact, F.action_mul_apply]
  cocycle q r s := by
    apply Subtype.ext
    change F.factor q r * F.factor (q * r) s = A q (F.factor r s) * F.factor q (r * s)
    rw [← hact]
    exact F.cocycle q r s

def jointFixedFactorInclusion (F : NonabelianFactorSystem L Q)
    (A : Q → L ≃ₗ⁅ℝ⁆ L) (hact : ∀ q x, F.action q x = A q x)
    (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (hcomm : ∀ S ∈ ss, ∀ q, Commute S.toLinearMap (A q).toLinearMap)
    (hfixed : ∀ S ∈ ss, ∀ q r, S (F.factor q r) = F.factor q r) :
    FactorExtension (jointFixedFactorSystem F A hact ss hcomm hfixed) →* FactorExtension F :=
  FactorExtension.map _ _
    (polynomialSubalgebraHom _ (jointFixedLieSubalgebra ss).incl)
    (fun q x => (hact q x).symm) (fun _ _ => rfl)

theorem jointFixedFactorInclusion_injective (F : NonabelianFactorSystem L Q)
    (A : Q → L ≃ₗ⁅ℝ⁆ L) (hact : ∀ q x, F.action q x = A q x)
    (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (hcomm : ∀ S ∈ ss, ∀ q, Commute S.toLinearMap (A q).toLinearMap)
    (hfixed : ∀ S ∈ ss, ∀ q r, S (F.factor q r) = F.factor q r) :
    Function.Injective (jointFixedFactorInclusion F A hact ss hcomm hfixed) :=
  FactorExtension.map_injective _ _ _ _ _ Subtype.val_injective

variable {G : Type} [Group G]

def jointFixedExtensionEmbedding (E : GroupExtension L G Q) (σ : E.Section) (hσ : σ 1 = 1)
    (A : Q → L ≃ₗ⁅ℝ⁆ L) (hact : ∀ q x, E.conjAct (σ q) x = A q x)
    (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (hcomm : ∀ S ∈ ss, ∀ q, Commute S.toLinearMap (A q).toLinearMap)
    (hfixed : ∀ S ∈ ss, ∀ q r, S (GroupExtensionSection.factor E σ q r) =
      GroupExtensionSection.factor E σ q r) :
    FactorExtension (jointFixedFactorSystem (GroupExtensionSection.factorSystem E σ hσ)
      A hact ss hcomm hfixed) →* G :=
  (GroupExtensionSection.mulEquiv E σ hσ).symm.toMonoidHom.comp
    (jointFixedFactorInclusion _ A hact ss hcomm hfixed)

theorem jointFixedExtensionEmbedding_injective (E : GroupExtension L G Q)
    (σ : E.Section) (hσ : σ 1 = 1)
    (A : Q → L ≃ₗ⁅ℝ⁆ L) (hact : ∀ q x, E.conjAct (σ q) x = A q x)
    (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (hcomm : ∀ S ∈ ss, ∀ q, Commute S.toLinearMap (A q).toLinearMap)
    (hfixed : ∀ S ∈ ss, ∀ q r, S (GroupExtensionSection.factor E σ q r) =
      GroupExtensionSection.factor E σ q r) :
    Function.Injective (jointFixedExtensionEmbedding E σ hσ A hact ss hcomm hfixed) :=
  (GroupExtensionSection.mulEquiv E σ hσ).symm.injective.comp
    (jointFixedFactorInclusion_injective _ A hact ss hcomm hfixed)

end PolycyclicRecognition

end

end OAI
