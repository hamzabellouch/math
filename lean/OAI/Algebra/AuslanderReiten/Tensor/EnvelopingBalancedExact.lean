import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingBalancedMap
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorFirst

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace ArExplicit.EnvelopingBimodule

universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {M N Q : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)}
variable [Module k M] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) M]
variable [Module k N] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) N]
variable [Module k Q] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) Q]

def mapRight (f : M ⟶ N) :
    EnvelopingBimodule k R M →ₗ[Rᵐᵒᵖ] EnvelopingBimodule k R N where
  toFun := map f
  map_add' := (map f).map_add
  map_smul' := map_right_smul f

theorem mapRight_injective (f : M ⟶ N) (hf : Function.Injective f.hom) :
    Function.Injective (mapRight f) := by
  intro x y h
  apply EnvelopingBimodule.ext
  apply hf
  exact congrArg EnvelopingBimodule.value h

theorem mapRight_surjective (f : M ⟶ N) (hf : Function.Surjective f.hom) :
    Function.Surjective (mapRight f) := by
  rintro ⟨y⟩
  obtain ⟨x, hx⟩ := hf y
  refine ⟨⟨x⟩, ?_⟩
  apply EnvelopingBimodule.ext
  exact hx

theorem mapRight_exact (f : M ⟶ N) (g : N ⟶ Q)
    (he : LinearMap.range f.hom = LinearMap.ker g.hom) :
    LinearMap.range (mapRight f) = LinearMap.ker (mapRight g) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    change mapRight g (mapRight f x) = 0
    apply EnvelopingBimodule.ext
    have h : f.hom x.value ∈ LinearMap.range f.hom := ⟨x.value, rfl⟩
    rw [he] at h
    exact h
  · intro hy
    have hy' : y.value ∈ LinearMap.ker g.hom := congrArg EnvelopingBimodule.value hy
    rw [← he] at hy'
    obtain ⟨x, hx⟩ := hy'
    refine ⟨⟨x⟩, ?_⟩
    apply EnvelopingBimodule.ext
    exact hx

variable (X : ModuleCat.{u} R) [Module k X]

@[simp] theorem mapFirst_mapRight_apply (f : M ⟶ N)
    (z : BalancedTensor k R (EnvelopingBimodule k R M) X) :
    BalancedTensor.mapFirst X (mapRight f) z = tensorMap X f z := rfl

theorem tensorMap_shortExact (f : M ⟶ N) (g : N ⟶ Q)
    (hf : Function.Injective f.hom) (hg : Function.Surjective g.hom)
    (he : LinearMap.range f.hom = LinearMap.ker g.hom)
    [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R Q)] :
    Function.Injective (tensorMap X f) ∧ Function.Surjective (tensorMap X g) ∧
      LinearMap.range (tensorMap X f) = LinearMap.ker (tensorMap X g) := by
  obtain ⟨hi, hs, hx⟩ := BalancedTensor.mapFirst_shortExact (k := k) (X := X)
    (mapRight f) (mapRight g) (mapRight_injective f hf)
    (mapRight_surjective g hg) (mapRight_exact f g he)
  refine ⟨hi, hs, ?_⟩
  ext z
  exact Iff.of_eq (congrArg (fun S : Submodule k (BalancedTensor k R (EnvelopingBimodule k R N) X) =>
    z ∈ S) hx)

end ArExplicit.EnvelopingBimodule

end

end OAI
