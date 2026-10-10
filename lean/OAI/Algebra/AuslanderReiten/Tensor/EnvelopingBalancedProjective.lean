import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingBalancedRegular
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Finiteness.Cardinality

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace ArExplicit.EnvelopingBimodule

universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (X : ModuleCat.{u} R) [Module k X] [IsScalarTower k R X]

private instance finitePiProjective {V : Type u} [AddCommGroup V] [Module R V]
    [Module.Projective R V] (n : ℕ) : Module.Projective R (Fin n → V) :=
  Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype :
    (Π₀ _ : Fin n, V) ≃ₗ[R] (Fin n → V))

instance regular_projective :
    Module.Projective R (BalancedTensor k R (EnvelopingBimodule k R (regularObject k R)) X) :=
  Module.Projective.of_equiv (regularEquiv k R X).symm

variable (M : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ))
variable [Module k M] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) M]

abbrev piObject (n : ℕ) : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ) :=
  ModuleCat.of (R ⊗[k] Rᵐᵒᵖ) (Fin n → M)

def piProjection (n : ℕ) (i : Fin n) : piObject M n ⟶ M :=
  ModuleCat.ofHom (LinearMap.proj i)

def piInclusion (n : ℕ) (i : Fin n) : M ⟶ piObject M n :=
  ModuleCat.ofHom (LinearMap.single (R ⊗[k] Rᵐᵒᵖ) (fun _ : Fin n => M) i)

def tensorPiCoordinates (n : ℕ) :
    BalancedTensor k R (EnvelopingBimodule k R (piObject M n)) X →ₗ[R]
      (Fin n → BalancedTensor k R (EnvelopingBimodule k R M) X) :=
  LinearMap.pi fun i => tensorMap X (piProjection M n i)

def tensorPiRecombine (n : ℕ) :
    (Fin n → BalancedTensor k R (EnvelopingBimodule k R M) X) →ₗ[R]
      BalancedTensor k R (EnvelopingBimodule k R (piObject M n)) X :=
  ∑ i, (tensorMap X (piInclusion M n i)).comp (LinearMap.proj i)

omit [IsScalarTower k R X] in
@[simp] theorem tensorPiRecombine_apply (n : ℕ)
    (v : Fin n → BalancedTensor k R (EnvelopingBimodule k R M) X) :
    tensorPiRecombine X M n v = ∑ i, tensorMap X (piInclusion M n i) (v i) := by
  simp only [tensorPiRecombine, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]

private theorem pi_reconstruct (n : ℕ) (f : EnvelopingBimodule k R (piObject M n)) :
    ∑ i, map (piInclusion M n i) (map (piProjection M n i) f) = f := by
  apply EnvelopingBimodule.ext
  change (scalarEquiv (piObject M n)) (∑ i, map (piInclusion M n i) (map (piProjection M n i) f)) = f.value
  rw [_root_.map_sum]
  change (∑ i, Pi.single i (f.value i)) = f.value
  exact Finset.univ_sum_single f.value

omit [IsScalarTower k R X] in
theorem tensorPi_retraction (n : ℕ) :
    (tensorPiRecombine X M n).comp (tensorPiCoordinates X M n) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  change tensorPiRecombine X M n (tensorPiCoordinates X M n z) = z
  induction z using BalancedTensor.induction_on with
  | zero => simp only [_root_.map_zero]
  | add z w hz hw => simp only [_root_.map_add, hz, hw]
  | tmul f x =>
    rw [tensorPiRecombine_apply]
    change (∑ i, tensorMap X (piInclusion M n i)
      (tensorMap X (piProjection M n i) (BalancedTensor.tmul f x))) = BalancedTensor.tmul f x
    simp only [tensorMap_tmul]
    change (∑ i, ((BalancedTensor.mk (k := k) (R := R)).flip x)
      (map (piInclusion M n i) (map (piProjection M n i) f))) = _
    rw [← _root_.map_sum, pi_reconstruct]
    rfl

omit [IsScalarTower k R X] in
theorem tensorPi_projective
    [Module.Projective R (BalancedTensor k R (EnvelopingBimodule k R M) X)] (n : ℕ) :
    Module.Projective R (BalancedTensor k R (EnvelopingBimodule k R (piObject M n)) X) :=
  Module.Projective.of_split (R := R) (tensorPiCoordinates X M n) (tensorPiRecombine X M n)
    (tensorPi_retraction X M n)

theorem tensor_projective [Module.Finite (R ⊗[k] Rᵐᵒᵖ) M]
    [Module.Projective (R ⊗[k] Rᵐᵒᵖ) M] :
    Module.Projective R (BalancedTensor k R (EnvelopingBimodule k R M) X) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' (R ⊗[k] Rᵐᵒᵖ) M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p
    (LinearMap.id : M →ₗ[R ⊗[k] Rᵐᵒᵖ] M) hp
  let := regular_projective (k := k) (R := R) X
  let : Module.Projective R (BalancedTensor k R
      (EnvelopingBimodule k R (piObject (regularObject k R) n)) X) :=
    tensorPi_projective X (regularObject k R) n
  apply Module.Projective.of_split (tensorMap X (ModuleCat.ofHom s))
    (tensorMap X (ModuleCat.ofHom p))
  rw [← tensorMap_comp]
  have hsp : ModuleCat.ofHom s ≫ ModuleCat.ofHom p = 𝟙 M := by
    apply ModuleCat.hom_ext
    exact hs
  rw [hsp, tensorMap_id]

end ArExplicit.EnvelopingBimodule

end

end OAI
