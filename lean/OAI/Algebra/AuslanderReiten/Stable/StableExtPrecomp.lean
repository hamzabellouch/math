import OAI.Algebra.AuslanderReiten.Complete.CompleteTailMap
import OAI.Algebra.AuslanderReiten.Stable.StableExtNaturality

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit
open CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {P Q : ChainComplex (ModuleCat.{u} R) ℤ}
variable (hP : TotallyAcyclicComplex P) (hQ : TotallyAcyclicComplex Q)
variable (f : P ⟶ Q) (N : ModuleCat.{u} R)

theorem positiveExtStableEquiv_precomp (n : ℕ)
    (x : Ext (ModuleCat.of R (Cokernel Q 0)) N (n+1)) :
    positiveExtStableEquiv (k := k) hP N n
      ((Ext.mk₀ (ModuleCat.ofHom (cokernelMap f 0))).comp x (zero_add _)) =
    StableHom.precomp (cokernelMap f ((n+1 : ℕ) : ℤ))
      (positiveExtStableEquiv (k := k) hQ N n x) := by
  obtain ⟨g, hg, rfl⟩ := (completeExtResolution hQ).extMk_surjective x (n+2) rfl
  rw [ProjectiveResolution.mk₀_comp_extMk g (n+2) rfl hg (completeTailHom f hP hQ),
    positiveExtStableEquiv_extMk, positiveExtStableEquiv_extMk]
  change StableHom.classOf R _ _ _ = StableHom.precomp _ (StableHom.classOf R _ _ _)
  rw [StableHom.precomp_classOf]
  apply congrArg (StableHom.classOf R _ _)
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range (P.d (((n+1 : ℕ) : ℤ)+1) ((n+1 : ℕ) : ℤ)).hom) z
  rfl

end ArExplicit

end

end OAI
