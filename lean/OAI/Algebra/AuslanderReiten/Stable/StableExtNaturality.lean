import OAI.Algebra.AuslanderReiten.Stable.StableExtEquiv

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory CategoryTheory.Abelian CompleteComparison
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {P : ChainComplex (ModuleCat.{u} R) ℤ} (hP : TotallyAcyclicComplex P)
variable {N N' : ModuleCat.{u} R}

theorem positiveExtStableEquiv_postcomp (n : ℕ) (g : N ⟶ N')
    (x : Ext (ModuleCat.of R (Cokernel P 0)) N (n+1)) :
    positiveExtStableEquiv (k := k) hP N' n
      (x.comp (Ext.mk₀ g) (add_zero _)) =
        StableHom.postcomp g.hom (positiveExtStableEquiv (k := k) hP N n x) := by
  obtain ⟨f, hf, rfl⟩ := (completeExtResolution hP).extMk_surjective x (n+2) rfl
  rw [ProjectiveResolution.extMk_comp_mk₀, positiveExtStableEquiv_extMk,
    positiveExtStableEquiv_extMk]
  change StableHom.classOf R _ _ _ = StableHom.postcomp g.hom (StableHom.classOf R _ _ _)
  rw [StableHom.postcomp_classOf]
  apply congrArg (StableHom.classOf R _ _)
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range (P.d (((n+1 : ℕ) : ℤ)+1) ((n+1 : ℕ) : ℤ)).hom) z
  rfl

end ArExplicit

end

end OAI
