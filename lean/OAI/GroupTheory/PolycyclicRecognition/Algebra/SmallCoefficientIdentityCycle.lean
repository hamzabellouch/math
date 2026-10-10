import OAI.GroupTheory.PolycyclicRecognition.Algebra.SmallCoefficientTensorAlgebra
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalizedIdentityConnecting

namespace OAI

/-! # The unit identity cocycles in the coefficient-ring tower

The ordinary integral resolution remains the source of the cochains. Their
coefficients are the same syzygies tensored with the small coefficient ring.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2300] TensorProduct.instModule
variable (G : Type) [Group G] [Countable G]

abbrev smallCoefficientTower : IntegralProjectiveTower G :=
  tensorNormalizedProjectiveTower (smallCoefficientRepresentation G)

def smallCoefficientIdentityCochain (n : ℕ) :
    (normalizedResolutionComplex (trivialIntegral G)).X n ⟶ (smallCoefficientTower G).obj n :=
  normalizedResolutionProjection (trivialIntegral G) n ≫
    smallCoefficientTensorUnit ((iteratedNormalizedSyzygy n).obj (trivialIntegral G))

theorem smallCoefficientIdentityCochain_closed (n : ℕ) :
    (normalizedResolutionComplex (trivialIntegral G)).d (n + 1) n ≫
      smallCoefficientIdentityCochain G n = 0 := by
  unfold smallCoefficientIdentityCochain
  erw [← Category.assoc, normalizedResolution_d_projection, zero_comp]

def smallCoefficientIdentityCycle (n : ℕ) :
    ((normalizedResolutionComplex (trivialIntegral G)).linearYonedaObj ℤ
      ((smallCoefficientTower G).obj n)).cycles n :=
  ((normalizedResolutionComplex (trivialIntegral G)).linearYonedaObj ℤ
      ((smallCoefficientTower G).obj n)).cyclesMk (smallCoefficientIdentityCochain G n)
    (n + 1) (by simp) (smallCoefficientIdentityCochain_closed G n)

def smallCoefficientIdentityClass (n : ℕ) :
    ((normalizedResolutionComplex (trivialIntegral G)).linearYonedaObj ℤ
      ((smallCoefficientTower G).obj n)).homology n :=
  ((normalizedResolutionComplex (trivialIntegral G)).linearYonedaObj ℤ
      ((smallCoefficientTower G).obj n)).homologyπ n (smallCoefficientIdentityCycle G n)

theorem smallCoefficientIdentityCycle_projection (n : ℕ) :
    ((normalizedResolutionComplex (trivialIntegral G)).linearYonedaObj ℤ
      ((smallCoefficientTower G).obj n)).iCycles n (smallCoefficientIdentityCycle G n) =
        smallCoefficientIdentityCochain G n := by
  exact ((normalizedResolutionComplex (trivialIntegral G)).linearYonedaObj ℤ
    ((smallCoefficientTower G).obj n)).i_cyclesMk (smallCoefficientIdentityCochain G n)
      (n + 1) (by simp) (smallCoefficientIdentityCochain_closed G n)

theorem smallCoefficientIdentityClass_connecting (n : ℕ) :
    (resolutionCoefficientSequence_shortExact (normalizedProjectiveResolution (trivialIntegral G))
      ((smallCoefficientTower G).sequence n) ((smallCoefficientTower G).shortExact n)).δ
        n (n + 1) rfl (smallCoefficientIdentityClass G n) =
      smallCoefficientIdentityClass G (n + 1) := by
  let P := normalizedProjectiveResolution (trivialIntegral G)
  let T := smallCoefficientTower G
  let S := T.sequence n
  let hS := resolutionCoefficientSequence_shortExact P S (T.shortExact n)
  let u := smallCoefficientTensorUnit (normalizedResolutionTerm (trivialIntegral G) n)
  have hz : ((forget₂ (ModuleCat ℤ) Ab).map
      ((resolutionCoefficientSequence P S).X₃.d n (n + 1)))
        (smallCoefficientIdentityCochain G n) = 0 :=
    smallCoefficientIdentityCochain_closed G n
  have hl : ((forget₂ (ModuleCat ℤ) Ab).map
      ((resolutionCoefficientSequence P S).g.f n)) u = smallCoefficientIdentityCochain G n := by
    change u ≫ T.π n = _
    exact (smallCoefficientTensorUnit_natural
      (normalizedFreeAugmentation ((iteratedNormalizedSyzygy n).obj (trivialIntegral G)))).symm
  have hd : ((forget₂ (ModuleCat ℤ) Ab).map
      ((resolutionCoefficientSequence P S).f.f (n + 1)))
        (smallCoefficientIdentityCochain G (n + 1)) =
      ((forget₂ (ModuleCat ℤ) Ab).map
        ((resolutionCoefficientSequence P S).X₂.d n (n + 1))) u := by
    change smallCoefficientIdentityCochain G (n + 1) ≫ T.ι n =
      (normalizedResolutionComplex (trivialIntegral G)).d (n + 1) n ≫ u
    unfold smallCoefficientIdentityCochain
    change (normalizedResolutionProjection (trivialIntegral G) (n + 1) ≫ _) ≫
      (tensorLeft (smallCoefficientRepresentation G)).map
        (kernel.ι (normalizedFreeAugmentation
          ((iteratedNormalizedSyzygy n).obj (trivialIntegral G)))) = _
    erw [Category.assoc, ← smallCoefficientTensorUnit_natural, ← Category.assoc,
      normalizedResolutionComplex_d]
    rfl
  exact hS.δ_apply n (n + 1) rfl (smallCoefficientIdentityCochain G n) hz
    u hl (smallCoefficientIdentityCochain G (n + 1)) hd (n + 2) (by simp)

end PolycyclicRecognition

end

end OAI
