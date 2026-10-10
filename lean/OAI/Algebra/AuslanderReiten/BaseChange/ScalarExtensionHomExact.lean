import OAI.Algebra.AuslanderReiten.BaseChange.ScalarExtensionHom

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit
universe u v w
variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]
  (R : Type w) [Ring R] [Algebra k R]
  {K L M N : Type w}
  [AddCommGroup K] [Module R K] [Module k K] [IsScalarTower k R K]
  [AddCommGroup L] [Module R L] [Module k L] [IsScalarTower k R L]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]

attribute [local instance] scalarExtensionModule

theorem scalarExtensionHom_exact
    [Module.Finite R K] [Module.Projective R K]
    [Module.Finite R L] [Module.Projective R L]
    [Module.Finite R M] [Module.Projective R M]
    (e : K →ₗ[R] L) (d : L →ₗ[R] M)
    (hex : Function.Exact (LinearMap.lcomp k N d) (LinearMap.lcomp k N e)) :
    Function.Exact
      (LinearMap.lcomp E (E ⊗[k] N) (scalarExtensionMap k E R d))
      (LinearMap.lcomp E (E ⊗[k] N) (scalarExtensionMap k E R e)) := by
  have hbase := Module.Flat.lTensor_exact E hex
  intro f
  constructor
  · intro hf
    obtain ⟨x, hx⟩ := (scalarExtensionHom_bijective k E R (M := L) (N := N)).2 f
    have hz : (LinearMap.lcomp k N e).lTensor E x = 0 := by
      apply (scalarExtensionHom_bijective k E R (M := K) (N := N)).1
      change scalarExtensionHom k E R ((LinearMap.lcomp k N e).baseChange E x) = _
      rw [scalarExtensionHom_precomp, hx, map_zero]
      exact hf
    obtain ⟨y, hy⟩ := (hbase x).1 hz
    refine ⟨scalarExtensionHom k E R y, ?_⟩
    change (scalarExtensionHom k E R y).comp (scalarExtensionMap k E R d) = f
    rw [← scalarExtensionHom_precomp]
    exact (congrArg (scalarExtensionHom k E R) hy).trans hx
  · rintro ⟨g, rfl⟩
    obtain ⟨y, rfl⟩ := (scalarExtensionHom_bijective k E R (M := M) (N := N)).2 g
    change ((scalarExtensionHom k E R y).comp (scalarExtensionMap k E R d)).comp
      (scalarExtensionMap k E R e) = 0
    rw [← scalarExtensionHom_precomp, ← scalarExtensionHom_precomp]
    change scalarExtensionHom k E R
      ((LinearMap.lcomp k N e).lTensor E ((LinearMap.lcomp k N d).lTensor E y)) = 0
    rw [(hbase _).2 ⟨y, rfl⟩, map_zero]

end ArExplicit

end

end OAI
