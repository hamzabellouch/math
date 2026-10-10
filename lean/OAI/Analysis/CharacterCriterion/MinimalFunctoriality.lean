import OAI.Analysis.CharacterCriterion.GeneralSystem

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.Spatial
open scoped TensorProduct
open UniformSpace
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
def flipL : Hilbert H K →L[ℂ] Hilbert K H :=
  (TensorProduct.commIsometry ℂ H K).toContinuousLinearEquiv.toContinuousLinearMap.completion
@[simp] lemma flipL_coe (x : H ⊗[ℂ] K) :
    flipL (x : Hilbert H K) = (TensorProduct.comm ℂ H K x : Hilbert K H) := by
  simp [flipL]
lemma flipL_flipL (x : Hilbert H K) : flipL (flipL x) = x := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (flipL.continuous.comp flipL.continuous) continuous_id
  | ih x => simp
lemma norm_flipL (x : Hilbert H K) : ‖flipL x‖ = ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (continuous_norm.comp flipL.continuous) continuous_norm
  | ih x => simp [TensorProduct.norm_comm]
def flip : Hilbert H K ≃ₗᵢ[ℂ] Hilbert K H where
  __ := flipL.toLinearMap
  invFun := flipL
  left_inv := flipL_flipL
  right_inv := flipL_flipL
  norm_map' := norm_flipL
@[simp] lemma flip_coe (x : H ⊗[ℂ] K) :
    flip (x : Hilbert H K) = (TensorProduct.comm ℂ H K x : Hilbert K H) := flipL_coe x
@[simp] lemma flip_symm : (flip (H:=H) (K:=K)).symm = flip := rfl
lemma flip_map (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
    flip.conjStarAlgEquiv (map T S) = map S T := by
  apply ext
  intro x
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, flip_symm,
    flip_coe, map_coe]
  congr 1
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul k h => simp
lemma norm_flip_conjugate (T : Hilbert H K →L[ℂ] Hilbert H K) :
    ‖(flip (H:=H) (K:=K)).conjStarAlgEquiv T‖=‖T‖ := by
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply]
  rw [ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

end KirchbergRordam.Spatial
namespace KirchbergRordam.MinTensor
open scoped TensorProduct CStarAlgebra
universe u
variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]
def algebraicFlip : (A ⊗[ℂ] B) ≃⋆ₐ[ℂ] (B ⊗[ℂ] A) :=
  StarAlgEquiv.ofAlgEquiv (_root_.Algebra.TensorProduct.comm ℂ A B) fun x => by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, star_add, hx, hy]
    | tmul a b => simp
@[simp] lemma algebraicFlip_tmul (a : A) (b : B) : algebraicFlip (a ⊗ₜ[ℂ] b) = b ⊗ₜ[ℂ] a := rfl
@[simp] lemma algebraicFlip_flip (x : A ⊗[ℂ] B) : algebraicFlip (algebraicFlip x) = x := by
  exact (_root_.Algebra.TensorProduct.comm ℂ A B).symm_apply_apply x

def RepresentationPair.rawMap (ρ : RepresentationPair A B) :
    (A ⊗[ℂ] B) →⋆ₐ[ℂ] (Spatial.Hilbert ρ.H ρ.K →L[ℂ] Spatial.Hilbert ρ.H ρ.K) :=
  MaxTensor.liftRaw (C := (Spatial.Hilbert ρ.H ρ.K →L[ℂ] Spatial.Hilbert ρ.H ρ.K)) ρ.left ρ.right ρ.commute
@[simp] lemma RepresentationPair.rawMap_tmul (ρ : RepresentationPair A B) (a : A) (b : B) :
    ρ.rawMap (a ⊗ₜ[ℂ] b) = ρ.left a * ρ.right b := rfl
def RepresentationPair.swap (ρ : RepresentationPair A B) : RepresentationPair B A where
  H := ρ.K
  K := ρ.H
  normH := inferInstance
  innerH := inferInstance
  completeH := inferInstance
  normK := inferInstance
  innerK := inferInstance
  completeK := inferInstance
  leftRep := ρ.rightRep
  rightRep := ρ.leftRep
lemma liftRaw_conjugate_swap {C E : Type*} [CStarAlgebra C] [CStarAlgebra E]
    (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C) (h : ∀ a b, Commute (φ a) (ψ b))
    (φ' : B →⋆ₐ[ℂ] E) (ψ' : A →⋆ₐ[ℂ] E) (h' : ∀ b a, Commute (φ' b) (ψ' a))
    (e : C ≃⋆ₐ[ℂ] E) (he₁ : ∀ b, φ' b=e (ψ b)) (he₂ : ∀ a, ψ' a=e (φ a))
    (x : A ⊗[ℂ] B) :
    MaxTensor.liftRaw φ' ψ' h' (algebraicFlip x) = e (MaxTensor.liftRaw φ ψ h x) := by
  change MaxTensor.liftRaw φ' ψ' h' (MaxTensor.rawEquiv (algebraicFlip x)) =
    e (MaxTensor.liftRaw φ ψ h (MaxTensor.rawEquiv x))
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul a b =>
    change MaxTensor.liftRaw φ' ψ' h' (algebraicFlip (a ⊗ₜ[ℂ] b)) =
      e (MaxTensor.liftRaw φ ψ h (a ⊗ₜ[ℂ] b))
    simp only [algebraicFlip_tmul,MaxTensor.liftRaw_tmul,he₁,he₂,←map_mul]
    exact congrArg e (h a b).symm.eq
lemma swap_left_flip (ρ : RepresentationPair A B) (b : B) :
    ρ.swap.left b=(Spatial.flip (H:=ρ.H) (K:=ρ.K)).conjStarAlgEquiv (ρ.right b) := by
  exact (Spatial.flip_map 1 (ρ.rightRep b)).symm
lemma swap_right_flip (ρ : RepresentationPair A B) (a : A) :
    ρ.swap.right a=(Spatial.flip (H:=ρ.H) (K:=ρ.K)).conjStarAlgEquiv (ρ.left a) := by
  exact (Spatial.flip_map (ρ.leftRep a) 1).symm
lemma liftRaw_swap (ρ : RepresentationPair A B) (x : A ⊗[ℂ] B) :
    ρ.swap.rawMap (algebraicFlip x) =
    (Spatial.flip (H:=ρ.H) (K:=ρ.K)).conjStarAlgEquiv (ρ.rawMap x) := by
  let e := (Spatial.flip (H:=ρ.H) (K:=ρ.K)).conjStarAlgEquiv
  have he0 : e 0=0 := map_zero (M:=Spatial.Hilbert ρ.H ρ.K →L[ℂ] Spatial.Hilbert ρ.H ρ.K)
    (N:=Spatial.Hilbert ρ.K ρ.H →L[ℂ] Spatial.Hilbert ρ.K ρ.H) e
  have headd (s t : Spatial.Hilbert ρ.H ρ.K →L[ℂ] Spatial.Hilbert ρ.H ρ.K) : e (s+t)=e s+e t :=
    e.toStarRingEquiv.toRingEquiv.map_add' s t
  have hemul (s t : Spatial.Hilbert ρ.H ρ.K →L[ℂ] Spatial.Hilbert ρ.H ρ.K) : e (s*t)=e s*e t :=
    e.toStarRingEquiv.toRingEquiv.map_mul' s t
  change ρ.swap.rawMap (algebraicFlip x) = e (ρ.rawMap x)
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add,map_add,map_add,headd,hx,hy]; rfl
  | tmul a b =>
    simp only [algebraicFlip_tmul,RepresentationPair.rawMap_tmul,swap_left_flip,swap_right_flip]
    change e (ρ.right b)*e (ρ.left a)=e (ρ.left a*ρ.right b)
    rw [←hemul,(ρ.commute a b).symm.eq]

lemma crossSeminorm_apply (ρ : RepresentationPair A B) (x : A ⊗[ℂ] B) :
    ρ.crossSeminorm.toSeminorm x = ‖ρ.rawMap x‖ := rfl
lemma crossSeminorm_swap (ρ : RepresentationPair A B) (x : A ⊗[ℂ] B) :
    ρ.swap.crossSeminorm.toSeminorm (algebraicFlip x) = ρ.crossSeminorm.toSeminorm x := by
  rw [crossSeminorm_apply,crossSeminorm_apply,liftRaw_swap]
  exact Spatial.norm_flip_conjugate _

lemma seminorm_algebraicFlip_le (x : A ⊗[ℂ] B) : seminorm (algebraicFlip x) ≤ seminorm x := by
  apply seminorm_le
  rintro (_|ρ)
  · exact apply_nonneg _ _
  · have h := crossSeminorm_swap ρ (algebraicFlip x)
    rw [algebraicFlip_flip] at h
    exact h.symm.le.trans (le_seminorm (some ρ.swap) x)
lemma seminorm_algebraicFlip (x : A ⊗[ℂ] B) : seminorm (algebraicFlip x) = seminorm x :=
  le_antisymm (seminorm_algebraicFlip_le x)
    (by simpa only [algebraicFlip_flip] using seminorm_algebraicFlip_le (algebraicFlip x))
def flipRaw : Raw A B →⋆ₐ[ℂ] Algebra B A :=
  of.comp ((rawEquiv.symm.trans (algebraicFlip.trans rawEquiv)).toStarAlgHom)
lemma norm_flipRaw (x : Raw A B) : ‖flipRaw x‖ = ‖x‖ := by
  change ‖of (rawEquiv (algebraicFlip (rawEquiv.symm x)))‖=‖x‖
  rw [norm_of]
  exact seminorm_algebraicFlip x
lemma continuous_flipRaw : Continuous (flipRaw (A:=A) (B:=B)) := by
  apply LipschitzWith.continuous (K:=1)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub, norm_flipRaw, le_refl]
def flipHom : Algebra A B →⋆ₐ[ℂ] Algebra B A where
  __ := UniformSpace.Completion.extensionHom (flipRaw (A:=A) (B:=B)).toRingHom continuous_flipRaw
  commutes' z := by
    change UniformSpace.Completion.extensionHom (flipRaw (A:=A) (B:=B)).toRingHom continuous_flipRaw
      ((algebraMap ℂ (Raw A B) z) : Algebra A B) = _
    rw [UniformSpace.Completion.extensionHom_coe]
    exact flipRaw.commutes z
  map_star' x := by
    induction x using UniformSpace.Completion.induction_on with
    | hp =>
      exact isClosed_eq
        (UniformSpace.Completion.continuous_extension.comp continuous_star)
        (continuous_star.comp UniformSpace.Completion.continuous_extension)
    | ih x =>
      change UniformSpace.Completion.extensionHom (flipRaw (A:=A) (B:=B)).toRingHom continuous_flipRaw
        (star (x : Algebra A B)) =
        star (UniformSpace.Completion.extensionHom (flipRaw (A:=A) (B:=B)).toRingHom continuous_flipRaw (x : Algebra A B))
      simp only [StarCompletion.star_coe, UniformSpace.Completion.extensionHom_coe]
      exact map_star flipRaw x
@[simp] lemma flipHom_of (x : Raw A B) : flipHom (of x) = flipRaw x :=
  UniformSpace.Completion.extensionHom_coe _ continuous_flipRaw x
@[simp] lemma flipHom_includeLeft (a : A) : flipHom (includeLeft (B:=B) a) = includeRight a := by
  change flipHom (of (rawEquiv (a ⊗ₜ[ℂ] (1 : B)))) = _
  rw [flipHom_of]
  rfl
@[simp] lemma flipHom_includeRight (b : B) : flipHom (includeRight (A:=A) b) = includeLeft b := by
  change flipHom (of (rawEquiv ((1 : A) ⊗ₜ[ℂ] b))) = _
  rw [flipHom_of]
  rfl
lemma flipHom_flipHom (x : Algebra A B) : flipHom (flipHom x) = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq ((map_continuous flipHom).comp (map_continuous flipHom)) continuous_id
  | ih y =>
    change flipHom (flipHom (of y))=of y
    rw [flipHom_of]
    change flipHom (of (rawEquiv (algebraicFlip (rawEquiv.symm y)))) = of y
    rw [flipHom_of]
    change of (rawEquiv (algebraicFlip (algebraicFlip (rawEquiv.symm y))))=of y
    simp only [algebraicFlip_flip, StarAlgEquiv.apply_symm_apply]


def flip : Algebra A B ≃⋆ₐ[ℂ] Algebra B A :=
  StarAlgEquiv.ofStarAlgHom flipHom flipHom
    (by ext x; exact flipHom_flipHom x) (by ext x; exact flipHom_flipHom x)
@[simp] lemma flip_includeLeft (a : A) : flip (includeLeft (B:=B) a)=includeRight a :=
  flipHom_includeLeft a
@[simp] lemma flip_includeRight (b : B) : flip (includeRight (A:=A) b)=includeLeft b :=
  flipHom_includeRight b
end KirchbergRordam.MinTensor
end

end OAI
