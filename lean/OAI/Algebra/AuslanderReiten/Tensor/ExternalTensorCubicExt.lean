import OAI.Algebra.AuslanderReiten.Ext.CubicExtAction
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorHomCubic
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorResolution

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [CharP k 2] [Module.Finite k A] [Module.Finite k B]
variable [HasDerivedCategory (ModuleCat.{u} (A ⊗[k] B))]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} A} {Y : ModuleCat.{u} B}
variable (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
variable (p : ∀ n, P.complex.X (n+3) ⟶ P.complex.X n)
variable (r : ∀ n, Q.complex.X (n+3) ⟶ Q.complex.X n)

def firstComparison (n : ℕ) : (projectiveResolution k A B P Q).complex.X (n+3) ⟶
    (projectiveResolution k A B P Q).complex.X n :=
  ModuleCat.ofHom (firstCubic k A B P.complex Q.complex p n)

def secondComparison (n : ℕ) : (projectiveResolution k A B P Q).complex.X (n+3) ⟶
    (projectiveResolution k A B P Q).complex.X n :=
  ModuleCat.ofHom (secondCubic k A B P.complex Q.complex r n)

variable (hp : ∀ n, p (n+1) ≫ P.complex.d (n+1) n = P.complex.d (n+4) (n+3) ≫ p n)
variable (hr : ∀ n, r (n+1) ≫ Q.complex.d (n+1) n = Q.complex.d (n+4) (n+3) ≫ r n)

include hp in
omit [Module.Finite k A] [Module.Finite k B]
  [HasDerivedCategory (ModuleCat.{u} (A ⊗[k] B))] in
theorem firstComparison_comm (n : ℕ) :
    firstComparison k A B P Q p (n+1) ≫ (projectiveResolution k A B P Q).complex.d (n+1) n =
      (projectiveResolution k A B P Q).complex.d (n+4) (n+3) ≫ firstComparison k A B P Q p n :=
  ModuleCat.hom_ext (firstCubic_chain k A B P.complex Q.complex p hp n)

include hr in
omit [Module.Finite k A] [Module.Finite k B]
  [HasDerivedCategory (ModuleCat.{u} (A ⊗[k] B))] in
theorem secondComparison_comm (n : ℕ) :
    secondComparison k A B P Q r (n+1) ≫ (projectiveResolution k A B P Q).complex.d (n+1) n =
      (projectiveResolution k A B P Q).complex.d (n+4) (n+3) ≫ secondComparison k A B P Q r n :=
  ModuleCat.hom_ext (secondCubic_chain k A B P.complex Q.complex r hr n)

def firstCubicExt : Ext (moduleObject k A B X Y) (moduleObject k A B X Y) 3 :=
  ResolutionProducts.endExt (projectiveResolution k A B P Q)
    (ResolutionProducts.natCubicCocycle (k := k) (projectiveResolution k A B P Q)
      (firstComparison k A B P Q p) (firstComparison_comm k A B P Q p hp))

def secondCubicExt : Ext (moduleObject k A B X Y) (moduleObject k A B X Y) 3 :=
  ResolutionProducts.endExt (projectiveResolution k A B P Q)
    (ResolutionProducts.natCubicCocycle (k := k) (projectiveResolution k A B P Q)
      (secondComparison k A B P Q r) (secondComparison_comm k A B P Q r hr))

omit [Module.Finite k A] [Module.Finite k B] in
theorem firstCubicExt_action {N : ModuleCat.{u} (A ⊗[k] B)} {n : ℕ}
    (f : (projectiveResolution k A B P Q).complex.X n ⟶ N)
    (hf : (projectiveResolution k A B P Q).complex.d (n+1) n ≫ f=0) :
    (firstCubicExt k A B P Q p hp).comp ((projectiveResolution k A B P Q).extMk f (n+1) rfl hf)
      (by omega : 3+n=n+3) =
      (projectiveResolution k A B P Q).extMk (firstComparison k A B P Q p n ≫ f) (n+4) rfl
        (ResolutionProducts.cubicPrecomp_closed (projectiveResolution k A B P Q)
          (firstComparison k A B P Q p) (firstComparison_comm k A B P Q p hp) f hf) :=
  ResolutionProducts.cubic_endExt_comp_extMk (k := k) (projectiveResolution k A B P Q)
    (firstComparison k A B P Q p) (firstComparison_comm k A B P Q p hp) f hf

omit [Module.Finite k A] [Module.Finite k B] in
theorem secondCubicExt_action {N : ModuleCat.{u} (A ⊗[k] B)} {n : ℕ}
    (f : (projectiveResolution k A B P Q).complex.X n ⟶ N)
    (hf : (projectiveResolution k A B P Q).complex.d (n+1) n ≫ f=0) :
    (secondCubicExt k A B P Q r hr).comp ((projectiveResolution k A B P Q).extMk f (n+1) rfl hf)
      (by omega : 3+n=n+3) =
      (projectiveResolution k A B P Q).extMk (secondComparison k A B P Q r n ≫ f) (n+4) rfl
        (ResolutionProducts.cubicPrecomp_closed (projectiveResolution k A B P Q)
          (secondComparison k A B P Q r) (secondComparison_comm k A B P Q r hr) f hf) :=
  ResolutionProducts.cubic_endExt_comp_extMk (k := k) (projectiveResolution k A B P Q)
    (secondComparison k A B P Q r) (secondComparison_comm k A B P Q r hr) f hf

end ArExplicit.ExternalTensor

end

end OAI
