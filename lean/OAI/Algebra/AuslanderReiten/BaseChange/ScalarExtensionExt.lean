import OAI.Algebra.AuslanderReiten.Ext.ExtBridge
import OAI.Algebra.AuslanderReiten.BaseChange.ScalarExtensionComplete

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit
universe u v w
variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]
  (R : Type w) [Ring R] [Algebra k R]
  (M N : Type w)
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower scalarExtensionModule

theorem PositiveExtVanish.scalarExtension
    (hgp : GorensteinProjective R M) (h : PositiveExtVanish R M N) :
    PositiveExtVanish (E ⊗[k] R) (E ⊗[k] M) (E ⊗[k] N) := by
  obtain ⟨P, hp, he, hd, ⟨e⟩⟩ := hgp
  let (i : ℤ) : Module.Finite R (P.X i) := (hp i).1
  let (i : ℤ) : Module.Projective R (P.X i) := (hp i).2
  let PE := scalarExtensionComplex k E R P
  have hpE (i : ℤ) : Module.Projective (E ⊗[k] R) (PE.X i) :=
    scalarExtension_projective k E R (P.X i)
  have heE (i : ℤ) : LinearMap.range (PE.d (i + 1) i).hom =
      LinearMap.ker (PE.d i (i - 1)).hom :=
    scalarExtensionComplex_exact k E R P he i
  let eE : (E ⊗[k] M) ≃ₗ[E ⊗[k] R] CompleteCokernel PE :=
    (scalarExtensionEquiv k E R e).trans
      (scalarExtensionCokernelEquiv k E R (P.d 1 0).hom).symm
  apply (positiveExtVanish_iff_completeResolution (E ⊗[k] R) (E ⊗[k] M)
    (E ⊗[k] N) PE hpE heE eE).2
  have hbase := (positiveExtVanish_iff_completeResolution R M N P
    (fun i => (hp i).2) he e).1 h
  intro n f hf
  have hex : Function.Exact
      (LinearMap.lcomp k N (P.d ((n + 1 : ℕ) : ℤ) (n : ℤ)).hom)
      (LinearMap.lcomp k N (P.d ((n + 2 : ℕ) : ℤ) ((n + 1 : ℕ) : ℤ)).hom) := by
    intro f
    constructor
    · intro hf
      obtain ⟨g, hg⟩ := hbase n f hf
      exact ⟨g, hg.symm⟩
    · rintro ⟨g, rfl⟩
      change (g.comp (P.d ((n + 1 : ℕ) : ℤ) (n : ℤ)).hom).comp
        (P.d ((n + 2 : ℕ) : ℤ) ((n + 1 : ℕ) : ℤ)).hom = 0
      rw [LinearMap.comp_assoc, show
        (P.d ((n + 1 : ℕ) : ℤ) (n : ℤ)).hom.comp
          (P.d ((n + 2 : ℕ) : ℤ) ((n + 1 : ℕ) : ℤ)).hom = 0 from
          congrArg ModuleCat.Hom.hom (P.d_comp_d _ _ _), LinearMap.comp_zero]
  have hE := scalarExtensionHom_exact k E R
    (P.d ((n + 2 : ℕ) : ℤ) ((n + 1 : ℕ) : ℤ)).hom
    (P.d ((n + 1 : ℕ) : ℤ) (n : ℤ)).hom hex
  obtain ⟨g, hg⟩ := (hE f).1 hf
  exact ⟨g, hg.symm⟩

end ArExplicit

end

end OAI
