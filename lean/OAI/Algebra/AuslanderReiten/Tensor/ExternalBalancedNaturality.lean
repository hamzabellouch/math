import OAI.Algebra.AuslanderReiten.Tensor.ExternalBalancedShuffle
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorFunctor
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorFunctor

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable {k A B : Type u} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower

def balancedMap {R : Type u} [Ring R] [Algebra k R]
    {M M' : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)} {X X' : ModuleCat.{u} R}
    (f : M ⟶ M') (g : X ⟶ X') :
    BalancedTensor k R (EnvelopingBimodule k R M) X →ₗ[R]
      BalancedTensor k R (EnvelopingBimodule k R M') X' :=
  (BalancedTensor.mapRight (k := k) (S := R) g.hom).comp
    (EnvelopingBimodule.tensorMap X f)

@[simp] theorem balancedMap_tmul {R : Type u} [Ring R] [Algebra k R]
    {M M' : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)} {X X' : ModuleCat.{u} R}
    (f : M ⟶ M') (g : X ⟶ X') (m : EnvelopingBimodule k R M) (x : X) :
    balancedMap f g (BalancedTensor.tmul m x) =
      BalancedTensor.tmul (EnvelopingBimodule.map f m) (g.hom x) := rfl

variable {M M' : ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)}
  {N N' : ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ)} {X X' : ModuleCat.{u} A} {Y Y' : ModuleCat.{u} B}
  (f : M ⟶ M') (g : N ⟶ N') (h : X ⟶ X') (j : Y ⟶ Y')

def exteriorMap :
    ExternalTensor.envelopingObject k A B
      (ExternalTensor.moduleObject k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ) M N) ⟶
    ExternalTensor.envelopingObject k A B
      (ExternalTensor.moduleObject k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ) M' N') :=
  (ExternalTensor.envelopingFunctor k A B).map
    (ExternalTensor.mapHom k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ) f g)

@[simp] theorem coordinates_map (m : EnvelopingBimodule k A M) (n : EnvelopingBimodule k B N) :
    EnvelopingBimodule.map (exteriorMap f g)
      ((bimoduleCoordinates k A B M N).symm (m ⊗ₜ[k] n)) =
    (bimoduleCoordinates k A B M' N').symm
      ((EnvelopingBimodule.map f m) ⊗ₜ[k] (EnvelopingBimodule.map g n)) := by
  apply EnvelopingBimodule.ext
  rfl

@[simp] theorem scalarCoordinates_map (x : X) (y : Y) :
    (ExternalTensor.mapHom k A B h j).hom
      ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y)) =
    (ExternalTensor.moduleScalarCoordinates k A B X' Y').symm
      ((h.hom x) ⊗ₜ[k] (j.hom y)) := rfl

theorem shuffle_natural :
    (shuffle k A B M' N' X' Y').toLinearMap.comp
      (balancedMap (exteriorMap f g) (ExternalTensor.mapHom k A B h j)) =
    (ExternalTensor.map k A B (balancedMap f h) (balancedMap g j)).comp
      (shuffle k A B M N X Y).toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul z w =>
    obtain ⟨z, rfl⟩ := (bimoduleCoordinates k A B M N).symm.surjective z
    obtain ⟨w, rfl⟩ := (ExternalTensor.moduleScalarCoordinates k A B X Y).symm.surjective w
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, BalancedTensor.add_tmul, hz, hz']
    | tmul m n =>
      induction w using TensorProduct.inductionOn with
      | add w w' hw hw' => simp only [map_add, BalancedTensor.tmul_add, hw, hw']
      | tmul x y =>
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, balancedMap_tmul,
          coordinates_map, scalarCoordinates_map, shuffle_pure, ExternalTensor.map_tmul]
        rfl

end ArExplicit.ExternalBalanced

end

end OAI
