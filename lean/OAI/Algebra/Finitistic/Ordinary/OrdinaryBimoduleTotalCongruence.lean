import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleCoefficientEquiv
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleTensorTotal

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleComplexTensor
universe u
variable (k S A : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable {Q Q' : CochainComplex (ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) ℤ}
variable (e : Q ≅ Q') (Z : CochainComplex (ModuleCat.{u} A) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

def rightTotalEquiv (n : ℤ) : totalTerm k S A Q Z p n ≃ₗ[S] totalTerm k S A Q' Z p n :=
  LinearEquiv.piCongrRight (fun i => rightTermEquiv k S A e Z (p i) (n + -(p i)))

theorem right_entry (n : ℤ) (i j : Fin l) :
    (rightTermEquiv k S A e Z (p j) ((n+1) + -(p j))).toLinearMap.comp
      (entry k S A Q Z p n i j) =
    (entry k S A Q' Z p n i j).comp
      (rightTermEquiv k S A e Z (p i) (n + -(p i))).toLinearMap := by
  unfold entry
  split_ifs with h
  · exact rightTermEquiv_map k S A e Z _ _ _ _ (eqToHom (congrArg Z.X (show n + -(p i) = (n+1) + -(p j) by omega)))
  · simp only [LinearMap.comp_zero,LinearMap.zero_comp]

theorem right_differential (n : ℤ) (z : totalTerm k S A Q Z p n) :
    rightTotalEquiv k S A e Z p (n+1) (differential k S A Q Z p n z) =
    differential k S A Q' Z p n (rightTotalEquiv k S A e Z p n z) := by
  funext j
  simp only [rightTotalEquiv,LinearEquiv.piCongrRight_apply,differential,
    LinearMap.pi_apply,LinearMap.add_apply,LinearMap.comp_apply,LinearMap.proj_apply,
    LinearMap.sum_apply,map_add,map_sum]
  apply congrArg₂ (· + ·)
  · change rightTermEquiv k S A e Z (p j) ((n+1) + -(p j))
        ((((-(p j)).negOnePow : ℤ)) • (map k S A Q Z (𝟙 _)
          (Z.d (n + -(p j)) ((n+1) + -(p j))) (z j))) =
      (((-(p j)).negOnePow : ℤ)) • (map k S A Q' Z (𝟙 _)
        (Z.d (n + -(p j)) ((n+1) + -(p j))))
        (rightTermEquiv k S A e Z (p j) (n + -(p j)) (z j))
    rw [map_zsmul]
    congr 1
    exact congrArg (fun f => f (z j)) (rightTermEquiv_map_id k S A e Z (p j) (n + -(p j)) ((n+1) + -(p j)) (Z.d (n + -(p j)) ((n+1) + -(p j))))
  · apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun f => f (z i)) (right_entry k S A e Z p n i j)

/-- Tensor total preserves actual isomorphisms of genuine bimodule complexes and their outside action. -/
def totalRightIso : total k S A Q Z p hp ≅ total k S A Q' Z p hp :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (rightTotalEquiv k S A e Z p n).toModuleIso) (by
    intro n m h
    change n+1=m at h
    subst m
    have h₁ : (total k S A Q Z p hp).d n (n+1) = ModuleCat.ofHom (differential k S A Q Z p n) :=
      CochainComplex.of_d (fun n => ModuleCat.of S (totalTerm k S A Q Z p n))
        (fun n => ModuleCat.ofHom (differential k S A Q Z p n)) n
    have h₂ : (total k S A Q' Z p hp).d n (n+1) = ModuleCat.ofHom (differential k S A Q' Z p n) :=
      CochainComplex.of_d (fun n => ModuleCat.of S (totalTerm k S A Q' Z p n))
        (fun n => ModuleCat.ofHom (differential k S A Q' Z p n)) n
    rw [h₁,h₂]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (right_differential k S A e Z p n z).symm)
end LittleFinitistic.BimoduleComplexTensor

end

end OAI
