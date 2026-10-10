import OAI.Algebra.AuslanderReiten.Stable.StableHom
import OAI.Algebra.AuslanderReiten.Complete.CompleteResolution

namespace OAI

noncomputable section
namespace ArExplicit
universe u
variable {R S₁ P₀ S₀ M B N : Type u} [Ring R]
variable [AddCommGroup S₁] [Module R S₁] [AddCommGroup P₀] [Module R P₀]
variable [AddCommGroup S₀] [Module R S₀] [AddCommGroup M] [Module R M]
variable [AddCommGroup B] [Module R B] [AddCommGroup N] [Module R N]
variable [Module.Finite R P₀] [Module.Projective R P₀]

theorem stable_connecting_congr (i : S₁ →ₗ[R] P₀) (π : P₀ →ₗ[R] S₀)
    (hπi : π.comp i = 0) (f : M →ₗ[R] B) (g : B →ₗ[R] N)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (he : LinearMap.range f = LinearMap.ker g)
    (s s' : S₀ →ₗ[R] N) (A A' : P₀ →ₗ[R] B) (t t' : S₁ →ₗ[R] M)
    (hA : g.comp A = s.comp π) (hA' : g.comp A' = s'.comp π)
    (ht : f.comp t = A.comp i) (ht' : f.comp t' = A'.comp i)
    (hs : StableHom.classOf R S₀ N s = StableHom.classOf R S₀ N s') :
    StableHom.classOf R S₁ M t = StableHom.classOf R S₁ M t' := by
  obtain ⟨Q, hQ, hRQ, hfree, hfin, j, v, hv⟩ := (StableHom.classOf_eq_iff s s').mp hs
  obtain ⟨vl, hvl⟩ := Module.projective_lifting_property g v hg
  let A₀ : P₀ →ₗ[R] B := A - A' - vl.comp (j.comp π)
  have hA₀ : g.comp A₀ = 0 := by
    ext z
    change g (A z - A' z - vl (j (π z))) = 0
    rw [map_sub, map_sub,
      show g (A z) = s (π z) from DFunLike.congr_fun hA z,
      show g (A' z) = s' (π z) from DFunLike.congr_fun hA' z,
      show g (vl (j (π z))) = v (j (π z)) from DFunLike.congr_fun hvl (j (π z))]
    change s (π z) - s' (π z) - v (j (π z)) = 0
    rw [show v (j (π z)) = s (π z) - s' (π z) from DFunLike.congr_fun hv (π z)]
    exact sub_self _
  obtain ⟨L, hL⟩ := lift_through_exact f g he A₀ hA₀
  have hdiff : L.comp i = t-t' := by
    ext z
    apply hf
    change f (L (i z)) = f (t z - t' z)
    rw [map_sub,
      show f (L (i z)) = A₀ (i z) from DFunLike.congr_fun hL (i z),
      show f (t z) = A (i z) from DFunLike.congr_fun ht z,
      show f (t' z) = A' (i z) from DFunLike.congr_fun ht' z]
    change A (i z) - A' (i z) - vl (j (π (i z))) = A (i z) - A' (i z)
    rw [show π (i z) = 0 from DFunLike.congr_fun hπi z, map_zero, map_zero, sub_zero]
  apply (StableHom.classOf_eq_iff t t').mpr
  apply (factorsThroughFiniteFree_iff_projective _).mpr
  exact ⟨P₀, inferInstance, inferInstance, inferInstance, inferInstance, i, L, hdiff⟩

end ArExplicit

end

end OAI
