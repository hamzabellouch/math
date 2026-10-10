import OAI.Algebra.AuslanderReiten.Stable.StableExt
import OAI.Algebra.AuslanderReiten.Resolutions.ResolutionHomology

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit
open CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {P : ChainComplex (ModuleCat.{u} R) ℤ} (hP : TotallyAcyclicComplex P)
variable (N : ModuleCat.{u} R)

abbrev completeExtResolution := completeCokernelResolution P hP.projective hP.exactAt

private theorem closed_of_indices {i j : ℤ} (h : i = j+1)
    (f : P.X j →ₗ[R] N) (hf : f.comp (P.d i j).hom = 0) :
    f.comp (P.d (j+1) j).hom = 0 := by
  subst i
  exact hf

theorem completeExtCycle_closed (n : ℕ)
    (f : LinearMap.ker (ResolutionHomology.differential (k := k) (Y := N)
      (completeExtResolution hP) (n+1))) :
    f.val.hom.comp (P.d (((n+1 : ℕ) : ℤ)+1) ((n+1 : ℕ) : ℤ)).hom = 0 := by
  have hf : (nonnegativeTail P).d (n+2) (n+1) ≫ f.val = 0 := f.property
  rw [nonnegativeTail_d] at hf
  exact closed_of_indices N (by omega : ((n+2 : ℕ) : ℤ) = ((n+1 : ℕ) : ℤ)+1)
    f.val.hom (congrArg ModuleCat.Hom.hom hf)

def completeExtCyclesMap (n : ℕ) :
    LinearMap.ker (ResolutionHomology.differential (k := k) (Y := N)
      (completeExtResolution hP) (n+1)) →ₗ[k]
        (Cokernel P ((n+1 : ℕ) : ℤ) →ₗ[R] N) where
  toFun f := completeExtCocycleMap ((n+1 : ℕ) : ℤ) f.val.hom (completeExtCycle_closed hP N n f)
  map_add' f g := by
    apply LinearMap.ext
    intro z
    obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (LinearMap.range
      (P.d (((n+1 : ℕ) : ℤ)+1) ((n+1 : ℕ) : ℤ)).hom) z
    rfl
  map_smul' a f := by
    apply LinearMap.ext
    intro z
    obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (LinearMap.range
      (P.d (((n+1 : ℕ) : ℤ)+1) ((n+1 : ℕ) : ℤ)).hom) z
    rfl

def completeExtCyclesStable (n : ℕ) :=
  (StableHom.classOfLinear k).comp (completeExtCyclesMap (k := k) hP N n)

theorem completeExtCyclesMap_surjective (n : ℕ) :
    Function.Surjective (completeExtCyclesMap (k := k) hP N n) := by
  intro f
  let π := (LinearMap.range (P.d (((n+1 : ℕ) : ℤ)+1) ((n+1 : ℕ) : ℤ)).hom).mkQ
  let g : (completeExtResolution hP).complex.X (n+1) ⟶ N := ModuleCat.ofHom (f.comp π)
  have hg : ResolutionHomology.differential (k := k) (completeExtResolution hP) (n+1) g = 0 := by
    change (nonnegativeTail P).d (n+2) (n+1) ≫ g = 0
    rw [nonnegativeTail_d]
    apply ModuleCat.hom_ext
    change (f.comp π).comp (P.d ((n+2 : ℕ) : ℤ) ((n+1 : ℕ) : ℤ)).hom = 0
    have hi : ((n+2 : ℕ) : ℤ) = ((n+1 : ℕ) : ℤ)+1 := by omega
    rw [hi, LinearMap.comp_assoc, LinearMap.range_mkQ_comp, LinearMap.comp_zero]
  refine ⟨⟨g,hg⟩, ?_⟩
  apply LinearMap.ext
  intro z
  obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (LinearMap.range
    (P.d (((n+1 : ℕ) : ℤ)+1) ((n+1 : ℕ) : ℤ)).hom) z
  rfl

theorem completeExtCyclesStable_surjective (n : ℕ) :
    Function.Surjective (completeExtCyclesStable (k := k) hP N n) :=
  StableHom.classOf_surjective.comp (completeExtCyclesMap_surjective hP N n)

theorem completeExtCyclesStable_kernel (n : ℕ) :
    LinearMap.ker (completeExtCyclesStable (k := k) hP N n) =
      LinearHomology.boundaries
        (ResolutionHomology.differential (k := k) (Y := N) (completeExtResolution hP) n)
        (ResolutionHomology.differential (completeExtResolution hP) (n+1))
        (ResolutionHomology.differential_comp (completeExtResolution hP) n) := by
  ext x
  change StableHom.classOf R _ N (completeExtCocycleMap ((n+1 : ℕ) : ℤ) x.val.hom
    (completeExtCycle_closed hP N n x)) = 0 ↔ _
  refine (completeExtCocycleMap_stable_zero_iff hP ((n+1 : ℕ) : ℤ)
    (show P.X ((n+1 : ℕ) : ℤ) →ₗ[R] N from x.val.hom) (completeExtCycle_closed hP N n x)).trans ?_
  have hprev : ((n+1 : ℕ) : ℤ)-1 = (n : ℤ) := by omega
  rw [hprev]
  constructor
  · rintro ⟨g,hg⟩
    refine ⟨ModuleCat.ofHom g, Subtype.ext ?_⟩
    apply ModuleCat.hom_ext
    change ((nonnegativeTail P).d (n+1) n ≫ ModuleCat.ofHom g).hom = x.val.hom
    rw [nonnegativeTail_d]
    exact hg
  · rintro ⟨g,hg⟩
    refine ⟨g.hom, ?_⟩
    have hh := congrArg (fun y => y.val.hom) hg
    change ((nonnegativeTail P).d (n+1) n ≫ g).hom = x.val.hom at hh
    rw [nonnegativeTail_d] at hh
    exact hh

def completeExtHomologyStableEquiv (n : ℕ) :
    LinearHomology.Homology
      (ResolutionHomology.differential (k := k) (Y := N) (completeExtResolution hP) n)
      (ResolutionHomology.differential (completeExtResolution hP) (n+1))
      (ResolutionHomology.differential_comp (completeExtResolution hP) n) ≃ₗ[k]
        StableHom R (Cokernel P ((n+1 : ℕ) : ℤ)) N :=
  (Submodule.quotEquivOfEq _ _ (completeExtCyclesStable_kernel hP N n).symm).trans
    ((completeExtCyclesStable hP N n).quotKerEquivOfSurjective
      (completeExtCyclesStable_surjective hP N n))

def positiveExtStableEquiv (n : ℕ) :
    Ext (ModuleCat.of R (Cokernel P 0)) N (n+1) ≃ₗ[k]
      StableHom R (Cokernel P ((n+1 : ℕ) : ℤ)) N :=
  (ResolutionHomology.extEquiv (k := k) (Y := N) (completeExtResolution hP) n).symm.trans
    (completeExtHomologyStableEquiv hP N n)

theorem positiveExtStableEquiv_extMk (n : ℕ)
    (f : (completeExtResolution hP).complex.X (n+1) ⟶ N)
    (hf : (completeExtResolution hP).complex.d (n+2) (n+1) ≫ f = 0) :
    positiveExtStableEquiv (k := k) hP N n
      ((completeExtResolution hP).extMk f (n+2) rfl hf) =
        completeExtCyclesStable (k := k) hP N n ⟨f,hf⟩ := by
  let z : LinearMap.ker (ResolutionHomology.differential (k := k) (Y := N)
    (completeExtResolution hP) (n+1)) := ⟨f,hf⟩
  have he : ResolutionHomology.extEquiv (k := k) (Y := N) (completeExtResolution hP) n
      (Submodule.Quotient.mk z) = (completeExtResolution hP).extMk f (n+2) rfl hf := rfl
  rw [← he]
  change completeExtHomologyStableEquiv hP N n
    ((ResolutionHomology.extEquiv (k := k) (Y := N) (completeExtResolution hP) n).symm
      ((ResolutionHomology.extEquiv (k := k) (Y := N) (completeExtResolution hP) n)
        (Submodule.Quotient.mk z))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

end ArExplicit

end

end OAI
