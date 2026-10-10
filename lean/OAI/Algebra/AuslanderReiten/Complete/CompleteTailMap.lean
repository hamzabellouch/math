import OAI.Algebra.AuslanderReiten.Stable.StableExtEquiv

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.CompleteComparison
universe u
variable {R : Type u} [Ring R]
variable {P Q : ChainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)

def nonnegativeTailMap : nonnegativeTail P ⟶ nonnegativeTail Q where
  f n := f.f (n : ℤ)
  comm' i j h := by
    change j+1=i at h
    subst i
    rw [nonnegativeTail_d, nonnegativeTail_d]
    exact f.comm _ _

theorem nonnegativeTailMap_augmentation :
    (nonnegativeTailMap f).f 0 ≫ (nonnegativeTailAugmentation Q).f 0 =
      (nonnegativeTailAugmentation P).f 0 ≫ ModuleCat.ofHom (cokernelMap f 0) := by
  rw [nonnegativeTailAugmentation_f_zero, nonnegativeTailAugmentation_f_zero]
  rfl

def completeTailHom (hP : TotallyAcyclicComplex P) (hQ : TotallyAcyclicComplex Q) :
    ProjectiveResolution.Hom (completeExtResolution hP) (completeExtResolution hQ)
      (ModuleCat.ofHom (cokernelMap f 0)) where
  hom := nonnegativeTailMap f
  hom_f_zero_comp_π_f_zero := by
    erw [ChainComplex.single₀_map_f_zero]
    exact nonnegativeTailMap_augmentation f

end ArExplicit.CompleteComparison

end

end OAI
