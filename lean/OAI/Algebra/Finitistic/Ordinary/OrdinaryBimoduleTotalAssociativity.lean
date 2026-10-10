import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleAssociativeTerms
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleTensorTotal

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleComplexTensor
universe u
variable (k S A B N : Type u) [Field k] [Ring S] [Ring A] [Ring B]
  [Algebra k S] [Algebra k A] [Algebra k B]
variable [AddCommGroup N] [Module k N] [Module A N] [Module Bᵐᵒᵖ N]
  [IsScalarTower k A N] [IsScalarTower k Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]
local instance : SMulCommClass Bᵐᵒᵖ A N := ⟨fun b a n => (smul_comm a b n).symm⟩
variable (Q : CochainComplex (ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) ℤ)
variable (Z : CochainComplex (ModuleCat.{u} B) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

def associativeTotalEquiv (n : ℤ) :
    totalTerm k S B (middleBimoduleComplex k S A B N Q) Z p n ≃ₗ[S]
      totalTerm k S A Q (middleLeftComplex k A B N Z) p n :=
  LinearEquiv.piCongrRight (fun i => associativeTermEquiv k S A B N Q Z (p i) (n + -(p i)))

theorem associative_entry (n : ℤ) (i j : Fin l) :
    (associativeTermEquiv k S A B N Q Z (p j) ((n+1) + -(p j))).toLinearMap.comp
      (entry k S B (middleBimoduleComplex k S A B N Q) Z p n i j) =
    (entry k S A Q (middleLeftComplex k A B N Z) p n i j).comp
      (associativeTermEquiv k S A B N Q Z (p i) (n + -(p i))).toLinearMap := by
  unfold entry
  split_ifs with h
  · have he : n + -(p i) = (n+1) + -(p j) := by omega
    have hh := associativeTermEquiv_map k S A B N Q Z (Q.d (p i) (p j)) (eqToHom (congrArg Z.X he))
    have ht : (middleLeftFunctor k A B N).map (eqToHom (congrArg Z.X he)) =
        eqToHom (congrArg (middleLeftComplex k A B N Z).X he) := by
      generalize n + -(p i) = q at he ⊢
      generalize (n+1) + -(p j) = q' at he ⊢
      subst q'
      simp only [eqToHom_refl,CategoryTheory.Functor.map_id]
      rfl
    rw [ht] at hh
    exact hh
  · simp only [LinearMap.comp_zero,LinearMap.zero_comp]

theorem associative_vertical (n : ℤ) (i : Fin l) :
    (associativeTermEquiv k S A B N Q Z (p i) ((n+1) + -(p i))).toLinearMap.comp
      (map k S B (middleBimoduleComplex k S A B N Q) Z (𝟙 _)
        (Z.d (n + -(p i)) ((n+1) + -(p i)))) =
    (map k S A Q (middleLeftComplex k A B N Z) (𝟙 _)
      ((middleLeftComplex k A B N Z).d (n + -(p i)) ((n+1) + -(p i)))).comp
      (associativeTermEquiv k S A B N Q Z (p i) (n + -(p i))).toLinearMap := by
  have h := associativeTermEquiv_map k S A B N Q Z (𝟙 (Q.X (p i)))
    (Z.d (n + -(p i)) ((n+1) + -(p i)))
  rw [(bimoduleTensorFunctor k S A Bᵐᵒᵖ N).map_id] at h
  exact h

theorem associative_differential (n : ℤ)
    (z : totalTerm k S B (middleBimoduleComplex k S A B N Q) Z p n) :
    associativeTotalEquiv k S A B N Q Z p (n+1)
      (differential k S B (middleBimoduleComplex k S A B N Q) Z p n z) =
    differential k S A Q (middleLeftComplex k A B N Z) p n
      (associativeTotalEquiv k S A B N Q Z p n z) := by
  funext j
  simp only [associativeTotalEquiv,LinearEquiv.piCongrRight_apply,differential,
    LinearMap.pi_apply,LinearMap.add_apply,LinearMap.comp_apply,LinearMap.proj_apply,
    LinearMap.sum_apply,map_add,map_sum]
  apply congrArg₂ (· + ·)
  · change associativeTermEquiv k S A B N Q Z (p j) ((n+1) + -(p j))
        ((((-(p j)).negOnePow : ℤ)) •
          (map k S B (middleBimoduleComplex k S A B N Q) Z (𝟙 _)
            (Z.d (n + -(p j)) ((n+1) + -(p j))) (z j))) =
      (((-(p j)).negOnePow : ℤ)) •
        (map k S A Q (middleLeftComplex k A B N Z) (𝟙 _)
          ((middleLeftComplex k A B N Z).d (n + -(p j)) ((n+1) + -(p j))))
          (associativeTermEquiv k S A B N Q Z (p j) (n + -(p j)) (z j))
    rw [map_zsmul]
    congr 1
    exact congrArg (fun f => f (z j)) (associative_vertical k S A B N Q Z p n j)
  · apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun f => f (z i)) (associative_entry k S A B N Q Z p n i j)

/-- Full signed total associativity in S-modules, on every input complex Z. -/
def totalAssociativityIso :
    total k S B (middleBimoduleComplex k S A B N Q) Z p hp ≅
      total k S A Q (middleLeftComplex k A B N Z) p hp :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (associativeTotalEquiv k S A B N Q Z p n).toModuleIso) (by
    intro n m h
    change n+1=m at h
    subst m
    have h₁ : (total k S B (middleBimoduleComplex k S A B N Q) Z p hp).d n (n+1) =
        ModuleCat.ofHom (differential k S B (middleBimoduleComplex k S A B N Q) Z p n) := CochainComplex.of_d
      (fun n => ModuleCat.of S (totalTerm k S B (middleBimoduleComplex k S A B N Q) Z p n))
      (fun n => ModuleCat.ofHom (differential k S B (middleBimoduleComplex k S A B N Q) Z p n)) n
    have h₂ : (total k S A Q (middleLeftComplex k A B N Z) p hp).d n (n+1) =
        ModuleCat.ofHom (differential k S A Q (middleLeftComplex k A B N Z) p n) := CochainComplex.of_d
      (fun n => ModuleCat.of S (totalTerm k S A Q (middleLeftComplex k A B N Z) p n))
      (fun n => ModuleCat.ofHom (differential k S A Q (middleLeftComplex k A B N Z) p n)) n
    rw [h₁,h₂]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (associative_differential k S A B N Q Z p n z).symm)
end LittleFinitistic.BimoduleComplexTensor

end

end OAI
