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
variable (Z : CochainComplex (ModuleCat.{u} L) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
open BimoduleComplexTensor

def firstTotalEquiv (n : ℤ) :
    totalTerm k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) p n ≃ₗ[L × R]
      BlockModule.Second k L R (totalTerm k R L O Z p n) :=
  (LinearEquiv.piCongrRight (fun i => firstTermEquiv k L R O T Z (p i) (n + -(p i)))).trans
    (show (∀ i : Fin l, BlockModule.Second k L R (term k R L O Z (p i) (n + -(p i)))) ≃ₗ[L × R]
      BlockModule.Second k L R (totalTerm k R L O Z p n) from LinearEquiv.refl _ _)

@[simp] theorem firstTotalEquiv_apply (n : ℤ)
    (z : totalTerm k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) p n)
    (i : Fin l) : firstTotalEquiv k L R O T Z p n z i =
      firstTermEquiv k L R O T Z (p i) (n + -(p i)) (z i) := rfl

theorem first_entry (n : ℤ) (i j : Fin l) :
    (firstTermEquiv k L R O T Z (p j) ((n+1) + -(p j))).toLinearMap.comp
      (entry k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) p n i j) =
    (BlockModule.secondMap k L R (entry k R L O Z p n i j)).comp
      (firstTermEquiv k L R O T Z (p i) (n + -(p i))).toLinearMap := by
  unfold entry
  split_ifs with h
  · have he : n + -(p i) = (n+1) + -(p j) := by omega
    have ht : (ProductModules.firstInflation L R).map (eqToHom (congrArg Z.X he)) =
        eqToHom (congrArg (BlockModule.firstComplex L R Z).X he) := by
      generalize n + -(p i) = q at he ⊢
      generalize (n+1) + -(p j) = q' at he ⊢
      subst q'
      simp only [eqToHom_refl,CategoryTheory.Functor.map_id]
      rfl
    have hh := firstTermEquiv_map k L R O T Z (O.d (p i) (p j)) (T.d (p i) (p j)) (eqToHom (congrArg Z.X he))
    rw [ht,← OffDiagonal.complex_d_all] at hh
    exact hh
  · apply LinearMap.ext
    intro x
    change firstTermEquiv k L R O T Z (p j) ((n+1) + -(p j)) 0 = 0
    exact (firstTermEquiv k L R O T Z (p j) ((n+1) + -(p j))).map_zero

theorem first_vertical (n : ℤ) (i : Fin l) :
    (firstTermEquiv k L R O T Z (p i) ((n+1) + -(p i))).toLinearMap.comp
      (map k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) (𝟙 _)
        ((BlockModule.firstComplex L R Z).d (n + -(p i)) ((n+1) + -(p i)))) =
    (BlockModule.secondMap k L R (map k R L O Z (𝟙 _) (Z.d (n + -(p i)) ((n+1) + -(p i))))).comp
      (firstTermEquiv k L R O T Z (p i) (n + -(p i))).toLinearMap := by
  exact firstTermEquiv_map k L R O T Z (𝟙 (O.X (p i))) (𝟙 (T.X (p i))) (Z.d _ _)

theorem first_differential (n : ℤ)
    (z : totalTerm k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) p n) :
    firstTotalEquiv k L R O T Z p (n+1)
      (differential k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) p n z) =
    differential k R L O Z p n (firstTotalEquiv k L R O T Z p n z) := by
  funext j
  change firstTermEquiv k L R O T Z (p j) ((n+1) + -(p j))
      (differential k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) p n z j) =
    differential k R L O Z p n (firstTotalEquiv k L R O T Z p n z) j
  simp only [differential,
    LinearMap.pi_apply,LinearMap.add_apply,LinearMap.comp_apply,LinearMap.proj_apply,
    LinearMap.sum_apply,map_add,map_sum]
  apply congrArg₂ (· + ·)
  · change firstTermEquiv k L R O T Z (p j) ((n+1) + -(p j))
        ((((-(p j)).negOnePow : ℤ)) •
          (map k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) (𝟙 _)
            ((BlockModule.firstComplex L R Z).d (n + -(p j)) ((n+1) + -(p j))) (z j))) =
      (((-(p j)).negOnePow : ℤ)) •
        (map k R L O Z (𝟙 _) (Z.d (n + -(p j)) ((n+1) + -(p j))))
          (firstTermEquiv k L R O T Z (p j) (n + -(p j)) (z j))
    rw [map_zsmul]
    congr 1
    exact congrArg (fun f => f (z j)) (first_vertical k L R O T Z p n j)
  · erw [LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun f => f (z i)) (first_entry k L R O T Z p n i j)

/-- Actual tensor with the off-diagonal complex on a first-block input is the second-block O-total. -/
def firstTotalIso :
    total k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) p hp ≅
      BlockModule.secondComplex L R (total k R L O Z p hp) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (firstTotalEquiv k L R O T Z p n).toModuleIso) (by
    intro n m h
    change n+1=m at h
    subst m
    have h₁ : (total k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) p hp).d n (n+1) =
        ModuleCat.ofHom (differential k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) p n) :=
      CochainComplex.of_d (fun n => ModuleCat.of (L × R) (totalTerm k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) p n))
        (fun n => ModuleCat.ofHom (differential k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) p n)) n
    have h₂ : (total k R L O Z p hp).d n (n+1) = ModuleCat.ofHom (differential k R L O Z p n) :=
      CochainComplex.of_d (fun n => ModuleCat.of R (totalTerm k R L O Z p n))
        (fun n => ModuleCat.ofHom (differential k R L O Z p n)) n
    change _ ≫ (ProductModules.secondInflation L R).map ((total k R L O Z p hp).d n (n+1)) = _
    rw [h₁,h₂]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (first_differential k L R O T Z p n z).symm)
end LittleFinitistic.OrdinarySimulation.BlockTensor

end

end OAI
