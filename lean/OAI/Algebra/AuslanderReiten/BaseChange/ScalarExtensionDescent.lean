import OAI.Algebra.AuslanderReiten.BaseChange.ScalarExtensionPresentation

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit
universe u v w
variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]

theorem exists_preimage_of_baseChange {V W : Type w}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (f : V →ₗ[k] W) (w : W)
    (h : ∃ x : E ⊗[k] V, f.baseChange E x = (1 : E) ⊗ₜ[k] w) :
    ∃ v : V, f v = w := by
  obtain ⟨x, hx⟩ := h
  let q := (LinearMap.range f).mkQ
  have hq : q.comp f = 0 := LinearMap.range_mkQ_comp f
  have hz : (1 : E) ⊗ₜ[k] q w = 0 := by
    change q.baseChange E ((1 : E) ⊗ₜ[k] w) = 0
    rw [← hx]
    change ((q.baseChange E).comp (f.baseChange E)) x = 0
    rw [← LinearMap.baseChange_comp, hq, LinearMap.baseChange_zero]
    rfl
  have hqw : q w = 0 := by
    apply Module.Flat.tensorProduct_mk_injective (R := k) (S := E)
      (M := W ⧸ LinearMap.range f)
    simpa using hz
  have hw : w ∈ LinearMap.ker q := hqw
  change w ∈ LinearMap.ker (LinearMap.range f).mkQ at hw
  rw [Submodule.ker_mkQ] at hw
  exact hw

variable (R : Type w) [Ring R] [Algebra k R]
  {M N L : Type w}
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
  [AddCommGroup L] [Module R L] [Module k L] [IsScalarTower k R L]

attribute [local instance] scalarExtensionModule

def moduleHomPostcomp (f : N →ₗ[R] L) : (M →ₗ[R] N) →ₗ[k] (M →ₗ[R] L) where
  toFun := f.comp
  map_add' g h := by
    ext x
    exact f.map_add _ _
  map_smul' a g := by
    ext m
    exact (f.restrictScalars k).map_smul a (g m)

theorem scalarExtensionHom_postcomp (f : N →ₗ[R] L) (x : E ⊗[k] (M →ₗ[R] N)) :
    scalarExtensionHom k E R ((moduleHomPostcomp k R f).baseChange E x) =
      (scalarExtensionMap k E R f).comp (scalarExtensionHom k E R x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.comp_add]
  | tmul e g =>
    simp only [LinearMap.baseChange_tmul, scalarExtensionHom_tmul]
    change e • scalarExtensionMap k E R (f.comp g) =
      (scalarExtensionMap k E R f).comp (e • scalarExtensionMap k E R g)
    rw [scalarExtensionMap_comp]
    ext z
    exact ((scalarExtensionMap k E R f).restrictScalars E).map_smul e
      (scalarExtensionMap k E R g z) |>.symm

theorem projective_of_scalarExtension [Module.Finite k R] [Module.Finite R M]
    [Module.Projective (E ⊗[k] R) (E ⊗[k] M)] : Module.Projective R M := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  obtain ⟨sE, hsE⟩ := Module.projective_lifting_property
    (scalarExtensionMap k E R p) (LinearMap.id : (E ⊗[k] M) →ₗ[E ⊗[k] R] (E ⊗[k] M))
    (scalarExtensionMap_surjective k E R p hp)
  obtain ⟨x, hx⟩ := (scalarExtensionHom_bijective_finite k E R
    (M := M) (N := Fin n → R)).2 sE
  have heq : (moduleHomPostcomp k R p).baseChange E x =
      (1 : E) ⊗ₜ[k] (LinearMap.id : M →ₗ[R] M) := by
    apply (scalarExtensionHom_bijective_finite k E R (M := M) (N := M)).1
    rw [scalarExtensionHom_postcomp, hx, hsE, scalarExtensionHom_tmul,
      scalarExtensionMap_id, one_smul]
  obtain ⟨s, hs⟩ := exists_preimage_of_baseChange k E (moduleHomPostcomp k R p)
    (LinearMap.id : M →ₗ[R] M) ⟨x, heq⟩
  change p.comp s = LinearMap.id at hs
  exact Module.Projective.of_split s p hs

theorem nonprojective_scalarExtension [Module.Finite k R] [Module.Finite R M]
    (h : ¬ Module.Projective R M) :
    ¬ Module.Projective (E ⊗[k] R) (E ⊗[k] M) := by
  intro hE
  let := hE
  exact h (projective_of_scalarExtension k E R)

end ArExplicit

end

end OAI
