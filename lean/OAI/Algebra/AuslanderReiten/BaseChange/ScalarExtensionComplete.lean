import OAI.Algebra.AuslanderReiten.Basic
import OAI.Algebra.AuslanderReiten.BaseChange.ScalarExtensionHomExact
import OAI.Algebra.AuslanderReiten.BaseChange.ScalarExtensionCokernel

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit
universe u v w
variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]
  (R : Type w) [Ring R] [Algebra k R]

@[instance_reducible]
def moduleCatBaseModule (M : ModuleCat.{w} R) : Module k M :=
  Module.compHom M (algebraMap k R)

attribute [local instance] moduleCatBaseModule

theorem moduleCatBaseTower (M : ModuleCat.{w} R) : IsScalarTower k R M :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] moduleCatBaseTower scalarExtensionModule

def scalarExtensionComplex (P : ChainComplex (ModuleCat.{w} R) ℤ) :
    ChainComplex (ModuleCat.{max v w} (E ⊗[k] R)) ℤ where
  X n := ModuleCat.of (E ⊗[k] R) (E ⊗[k] P.X n)
  d i j := ModuleCat.ofHom (scalarExtensionMap k E R (P.d i j).hom)
  shape i j hij := by
    rw [P.shape i j hij]
    apply ModuleCat.hom_ext
    exact map_zero (scalarExtensionHomLinear k E R)
  d_comp_d' i j l _ _ := by
    apply ModuleCat.hom_ext
    change (scalarExtensionMap k E R (P.d j l).hom).comp
      (scalarExtensionMap k E R (P.d i j).hom) = 0
    rw [← scalarExtensionMap_comp]
    rw [show (P.d j l).hom.comp (P.d i j).hom = 0 from
      congrArg ModuleCat.Hom.hom (P.d_comp_d i j l)]
    exact map_zero (scalarExtensionHomLinear k E R)

theorem scalarExtensionComplex_exact (P : ChainComplex (ModuleCat.{w} R) ℤ)
    (h : ∀ n : ℤ, LinearMap.range (P.d (n + 1) n).hom =
      LinearMap.ker (P.d n (n - 1)).hom) (n : ℤ) :
    LinearMap.range ((scalarExtensionComplex k E R P).d (n + 1) n).hom =
      LinearMap.ker ((scalarExtensionComplex k E R P).d n (n - 1)).hom :=
  (LinearMap.exact_iff.mp (scalarExtensionMap_exact k E R _ _
    (LinearMap.exact_iff.mpr (h n).symm))).symm

theorem scalarExtensionComplex_dualExact (P : ChainComplex (ModuleCat.{w} R) ℤ)
    (hp : ∀ n : ℤ, Module.Finite R (P.X n) ∧ Module.Projective R (P.X n))
    (hd : ∀ (n : ℤ) (f : P.X n →ₗ[R] R),
      f.comp (P.d (n + 1) n).hom = 0 →
      ∃ g : P.X (n - 1) →ₗ[R] R, f = g.comp (P.d n (n - 1)).hom)
    (n : ℤ) (f : (scalarExtensionComplex k E R P).X n →ₗ[E ⊗[k] R] (E ⊗[k] R))
    (hf : f.comp ((scalarExtensionComplex k E R P).d (n + 1) n).hom = 0) :
    ∃ g : (scalarExtensionComplex k E R P).X (n - 1) →ₗ[E ⊗[k] R] (E ⊗[k] R),
      f = g.comp ((scalarExtensionComplex k E R P).d n (n - 1)).hom := by
  let (index : ℤ) : Module.Finite R (P.X index) := (hp index).1
  let (index : ℤ) : Module.Projective R (P.X index) := (hp index).2
  have he : Function.Exact (LinearMap.lcomp k R (P.d n (n - 1)).hom)
      (LinearMap.lcomp k R (P.d (n + 1) n).hom) := by
    intro f
    constructor
    · intro hf
      obtain ⟨g, hg⟩ := hd n f hf
      exact ⟨g, hg.symm⟩
    · rintro ⟨g, rfl⟩
      change (g.comp (P.d n (n - 1)).hom).comp (P.d (n + 1) n).hom = 0
      rw [LinearMap.comp_assoc, show (P.d n (n - 1)).hom.comp
        (P.d (n + 1) n).hom = 0 from congrArg ModuleCat.Hom.hom (P.d_comp_d _ _ _),
        LinearMap.comp_zero]
  have hE := scalarExtensionHom_exact k E R (P.d (n + 1) n).hom (P.d n (n - 1)).hom he
  let H (I : Module (E ⊗[k] R) (E ⊗[k] R)) : Prop :=
    letI := I
    ∀ (f : (scalarExtensionComplex k E R P).X n →ₗ[E ⊗[k] R] (E ⊗[k] R)),
      f.comp ((scalarExtensionComplex k E R P).d (n + 1) n).hom = 0 →
      ∃ g : (scalarExtensionComplex k E R P).X (n - 1) →ₗ[E ⊗[k] R] (E ⊗[k] R),
        f = g.comp ((scalarExtensionComplex k E R P).d n (n - 1)).hom
  have hraw : H (scalarExtensionModule k E R R) := by
    intro f hf
    obtain ⟨g, hg⟩ := (hE f).1 hf
    exact ⟨g, hg.symm⟩
  rw [scalarExtensionModule_eq_regular k E R] at hraw
  exact hraw f hf

theorem GorensteinProjective.scalarExtension
    (M : Type w) [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
    (h : GorensteinProjective R M) :
    GorensteinProjective (E ⊗[k] R) (E ⊗[k] M) := by
  obtain ⟨P, hp, he, hd, ⟨e⟩⟩ := h
  refine ⟨scalarExtensionComplex k E R P, ?_, ?_, ?_, ?_⟩
  · intro n
    let := (hp n).1
    let := (hp n).2
    exact ⟨scalarExtension_finite k E R (P.X n), scalarExtension_projective k E R (P.X n)⟩
  · exact scalarExtensionComplex_exact k E R P he
  · exact scalarExtensionComplex_dualExact k E R P hp hd
  · exact ⟨(scalarExtensionEquiv k E R e).trans
      (scalarExtensionCokernelEquiv k E R (P.d 1 0).hom).symm⟩

end ArExplicit

end

end OAI
