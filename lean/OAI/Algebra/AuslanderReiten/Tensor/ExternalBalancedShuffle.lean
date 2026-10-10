import OAI.Algebra.AuslanderReiten.Tensor.ExternalBalancedEquiv
import OAI.Algebra.AuslanderReiten.Tensor.ExternalBalancedCoordinates

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (M : ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) (N : ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ))
  (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
local notation "FM" => EnvelopingBimodule k A M
local notation "FN" => EnvelopingBimodule k B N
local notation "BM" => BalancedTensor k A FM X
local notation "BN" => BalancedTensor k B FN Y
local notation "Src" => BalancedTensor k (A ⊗[k] B) (exteriorBimodule k A B M N)
  (ExternalTensor.moduleObject k A B X Y)
local notation "Tgt" => ExternalTensor.moduleObject k A B BM BN

def scalarShuffle : Src ≃ₗ[k] BM ⊗[k] BN :=
  equiv (bimoduleCoordinates k A B M N) (ExternalTensor.moduleScalarCoordinates k A B X Y)
    (bimoduleCoordinates_right k A B M N) (fun _ _ _ _ => rfl)

@[simp] theorem scalarShuffle_pure (m : FM) (n : FN) (x : X) (y : Y) :
    scalarShuffle k A B M N X Y
      (BalancedTensor.tmul ((bimoduleCoordinates k A B M N).symm (m ⊗ₜ[k] n))
        ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y))) =
      BalancedTensor.tmul (R := A) m x ⊗ₜ[k] BalancedTensor.tmul (R := B) n y :=
  equiv_pure _ _ _ _ m n x y

theorem scalarShuffle_smul (r : A ⊗[k] B) (z : Src) :
    scalarShuffle k A B M N X Y (r • z) =
      ExternalTensor.representation k A B BM BN r (scalarShuffle k A B M N X Y z) := by
  induction r using TensorProduct.inductionOn with
  | add r s hr hs => simp only [add_smul, map_add, LinearMap.add_apply, hr, hs]
  | tmul a b =>
    induction z using BalancedTensor.induction_on with
    | zero => simp
    | add z w hz hw => simp only [smul_add, map_add, hz, hw]
    | tmul z w =>
      obtain ⟨z, rfl⟩ := (bimoduleCoordinates k A B M N).symm.surjective z
      obtain ⟨w, rfl⟩ := (ExternalTensor.moduleScalarCoordinates k A B X Y).symm.surjective w
      induction z using TensorProduct.inductionOn with
      | add z z' hz hz' => simp only [map_add, BalancedTensor.add_tmul, smul_add, hz, hz']
      | tmul m n =>
        induction w using TensorProduct.inductionOn with
        | add w w' hw hw' => simp only [map_add, BalancedTensor.tmul_add, smul_add, hw, hw']
        | tmul x y =>
          rw [BalancedTensor.smul_tmul, bimoduleCoordinates_left, scalarShuffle_pure,
            scalarShuffle_pure]
          rfl

def shuffle : Src ≃ₗ[A ⊗[k] B] Tgt where
  __ := (scalarShuffle k A B M N X Y).toAddEquiv
  map_smul' := scalarShuffle_smul k A B M N X Y

@[simp] theorem shuffle_pure (m : FM) (n : FN) (x : X) (y : Y) :
    shuffle k A B M N X Y
      (BalancedTensor.tmul ((bimoduleCoordinates k A B M N).symm (m ⊗ₜ[k] n))
        ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y))) =
      (BalancedTensor.tmul (R := A) m x ⊗ₜ[k] BalancedTensor.tmul (R := B) n y : Tgt) :=
  scalarShuffle_pure k A B M N X Y m n x y

end ArExplicit.ExternalBalanced

end

end OAI
