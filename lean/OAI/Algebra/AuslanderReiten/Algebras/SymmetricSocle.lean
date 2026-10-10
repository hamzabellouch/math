import OAI.Algebra.AuslanderReiten.Algebras.FrobeniusTrace
import OAI.Algebra.AuslanderReiten.Stable.StableHom
import Mathlib.RingTheory.Ideal.Defs

namespace OAI

namespace ArExplicit.FrobeniusTrace

universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (τ : FrobeniusTrace k R)
variable (hs : ∀ a b : R, τ.trace (a * b) = τ.trace (b * a))
variable (J : Ideal R) [J.IsTwoSided]

include τ hs

theorem annihilator_right {u : R} (hu : ∀ j ∈ J, j * u = 0) {j : R} (hj : j ∈ J) :
    u * j = 0 := by
  apply τ.separates
  intro a
  rw [← mul_assoc, hs, ← mul_assoc, hu (j * a) (J.mul_mem_right a hj), map_zero]

variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (hM : ∀ j ∈ J, ∀ x : M, j • x = 0)
variable (ι : N →ₗ[R] R) (hι : Function.Injective ι) (hN : ∀ x : N, ι x ∈ J)

include hM hι hN

theorem factor_fin_zero (n : ℕ) (g : M →ₗ[R] (Fin n → R)) (p : (Fin n → R) →ₗ[R] N) :
    p.comp g = 0 := by
  apply LinearMap.ext
  intro x
  apply hι
  change ι (p (g x)) = ι 0
  rw [map_zero]
  have he : g x = ∑ j : Fin n, g x j • Pi.single j (1 : R) := by
    ext j
    simp [Pi.single_apply]
  rw [he, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  simp only [map_smul, smul_eq_mul]
  apply τ.annihilator_right hs J _ (hN _)
  intro r hr
  let gj : M →ₗ[R] R := (LinearMap.proj j).comp g
  change r • gj x = 0
  rw [← gj.map_smul, hM r hr x, map_zero]

theorem projective_factor_zero (f : M →ₗ[R] N)
    (hf : FactorsThroughFiniteProjective R M N f) : f = 0 := by
  rcases hf with ⟨P, hP, hRP, hp, hfinite, i, p, rfl⟩
  let := hP
  let := hRP
  let := hp
  let := hfinite
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R P
  obtain ⟨s, hspl⟩ := Module.projective_lifting_property π (LinearMap.id : P →ₗ[R] P) hπ
  have hz := τ.factor_fin_zero hs J hM ι hι hN n (s.comp i) (p.comp π)
  have he : (p.comp π).comp (s.comp i) = p.comp i := by
    apply LinearMap.ext
    intro x
    have hh := LinearMap.congr_fun hspl (i x)
    change π (s (i x)) = i x at hh
    exact congrArg p hh
  rw [he] at hz
  exact hz

theorem stable_class_ne_zero {f : M →ₗ[R] N} (hf : f ≠ 0) :
    StableHom.classOf R M N f ≠ 0 := by
  intro hz
  exact hf (τ.projective_factor_zero hs J hM ι hι hN f
    ((StableHom.classOf_eq_zero_iff_projective f).mp hz))

end ArExplicit.FrobeniusTrace

end OAI
