import OAI.Algebra.Finitistic.Ordinary.OrdinaryBlockTensorTerms
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleTensorTotal

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.BlockTensor
universe u
variable (k L R : Type u) [Field k] [Ring L] [Ring R] [Algebra k L] [Algebra k R]
variable (O : CochainComplex (ModuleCat.{u} (R ⊗[k] Lᵐᵒᵖ)) ℤ)
variable (T : CochainComplex (ModuleCat.{u} (L ⊗[k] Rᵐᵒᵖ)) ℤ)
variable (Z : CochainComplex (ModuleCat.{u} R) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
open BimoduleComplexTensor

def secondTotalEquiv (n : ℤ) :
    totalTerm k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) p n ≃ₗ[L × R]
      BlockModule.First k L R (totalTerm k L R T Z p n) :=
  (LinearEquiv.piCongrRight (fun i => secondTermEquiv k L R O T Z (p i) (n + -(p i)))).trans
    (show (∀ i : Fin l, BlockModule.First k L R (term k L R T Z (p i) (n + -(p i)))) ≃ₗ[L × R]
      BlockModule.First k L R (totalTerm k L R T Z p n) from LinearEquiv.refl _ _)

@[simp] theorem secondTotalEquiv_apply (n : ℤ)
    (z : totalTerm k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) p n)
    (i : Fin l) : secondTotalEquiv k L R O T Z p n z i =
      secondTermEquiv k L R O T Z (p i) (n + -(p i)) (z i) := rfl

theorem second_entry (n : ℤ) (i j : Fin l) :
    (secondTermEquiv k L R O T Z (p j) ((n+1) + -(p j))).toLinearMap.comp
      (entry k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) p n i j) =
    (BlockModule.firstMap k L R (entry k L R T Z p n i j)).comp
      (secondTermEquiv k L R O T Z (p i) (n + -(p i))).toLinearMap := by
  unfold entry
  split_ifs with h
  · have he : n + -(p i) = (n+1) + -(p j) := by omega
    have ht : (ProductModules.secondInflation L R).map (eqToHom (congrArg Z.X he)) =
        eqToHom (congrArg (BlockModule.secondComplex L R Z).X he) := by
      generalize n + -(p i) = q at he ⊢
      generalize (n+1) + -(p j) = q' at he ⊢
      subst q'
      simp only [eqToHom_refl,CategoryTheory.Functor.map_id]
      rfl
    have hh := secondTermEquiv_map k L R O T Z (O.d (p i) (p j)) (T.d (p i) (p j)) (eqToHom (congrArg Z.X he))
    rw [ht,← OffDiagonal.complex_d_all] at hh
    exact hh
  · apply LinearMap.ext
    intro x
    change secondTermEquiv k L R O T Z (p j) ((n+1) + -(p j)) 0 = 0
    exact (secondTermEquiv k L R O T Z (p j) ((n+1) + -(p j))).map_zero

theorem second_vertical (n : ℤ) (i : Fin l) :
    (secondTermEquiv k L R O T Z (p i) ((n+1) + -(p i))).toLinearMap.comp
      (map k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) (𝟙 _)
        ((BlockModule.secondComplex L R Z).d (n + -(p i)) ((n+1) + -(p i)))) =
    (BlockModule.firstMap k L R (map k L R T Z (𝟙 _) (Z.d (n + -(p i)) ((n+1) + -(p i))))).comp
      (secondTermEquiv k L R O T Z (p i) (n + -(p i))).toLinearMap := by
  exact secondTermEquiv_map k L R O T Z (𝟙 (O.X (p i))) (𝟙 (T.X (p i))) (Z.d _ _)

theorem second_differential (n : ℤ)
    (z : totalTerm k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) p n) :
    secondTotalEquiv k L R O T Z p (n+1)
      (differential k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) p n z) =
    differential k L R T Z p n (secondTotalEquiv k L R O T Z p n z) := by
  funext j
  change secondTermEquiv k L R O T Z (p j) ((n+1) + -(p j))
      (differential k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) p n z j) =
    differential k L R T Z p n (secondTotalEquiv k L R O T Z p n z) j
  simp only [differential,
    LinearMap.pi_apply,LinearMap.add_apply,LinearMap.comp_apply,LinearMap.proj_apply,
    LinearMap.sum_apply,map_add,map_sum]
  apply congrArg₂ (· + ·)
  · change secondTermEquiv k L R O T Z (p j) ((n+1) + -(p j))
        ((((-(p j)).negOnePow : ℤ)) •
          (map k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) (𝟙 _)
            ((BlockModule.secondComplex L R Z).d (n + -(p j)) ((n+1) + -(p j))) (z j))) =
      (((-(p j)).negOnePow : ℤ)) •
        (map k L R T Z (𝟙 _) (Z.d (n + -(p j)) ((n+1) + -(p j))))
          (secondTermEquiv k L R O T Z (p j) (n + -(p j)) (z j))
    rw [map_zsmul]
    congr 1
    exact congrArg (fun f => f (z j)) (second_vertical k L R O T Z p n j)
  · erw [LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun f => f (z i)) (second_entry k L R O T Z p n i j)

/-- Actual tensor with the off-diagonal complex on a second-block input is the first-block T-total. -/
def secondTotalIso :
    total k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) p hp ≅
      BlockModule.firstComplex L R (total k L R T Z p hp) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (secondTotalEquiv k L R O T Z p n).toModuleIso) (by
    intro n m h
    change n+1=m at h
    subst m
    have h₁ : (total k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) p hp).d n (n+1) =
        ModuleCat.ofHom (differential k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) p n) :=
      CochainComplex.of_d (fun n => ModuleCat.of (L × R) (totalTerm k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) p n))
        (fun n => ModuleCat.ofHom (differential k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) p n)) n
    have h₂ : (total k L R T Z p hp).d n (n+1) = ModuleCat.ofHom (differential k L R T Z p n) :=
      CochainComplex.of_d (fun n => ModuleCat.of L (totalTerm k L R T Z p n))
        (fun n => ModuleCat.ofHom (differential k L R T Z p n)) n
    change _ ≫ (ProductModules.firstInflation L R).map ((total k L R T Z p hp).d n (n+1)) = _
    rw [h₁,h₂]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (second_differential k L R O T Z p n z).symm)
end LittleFinitistic.OrdinarySimulation.BlockTensor

end

end OAI
