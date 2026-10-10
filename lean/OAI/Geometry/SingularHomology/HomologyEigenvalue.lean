import Mathlib

namespace OAI

noncomputable section

namespace Problem340

theorem exists_eigenvector_of_scalar_quotient
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] V) (P : V →ₗ[K] W) (μ : K)
    (hP : P ≠ 0) (hPA : P.comp A = μ • P) :
    ∃ v : V, v ≠ 0 ∧ A v = μ • v := by
  by_contra h
  have hker : ∀ v : V, (A - μ • (LinearMap.id : V →ₗ[K] V)) v = 0 → v = 0 := by
    intro v hv
    by_contra hv0
    apply h
    refine ⟨v, hv0, ?_⟩
    simpa using (sub_eq_zero.mp hv)
  have hinj : Function.Injective (A - μ • (LinearMap.id : V →ₗ[K] V)) := by
    intro x y hxy
    have hz : (A - μ • (LinearMap.id : V →ₗ[K] V)) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hker (x - y) hz)
  have hsurj := LinearMap.surjective_of_injective hinj
  apply hP
  ext v
  obtain ⟨w, rfl⟩ := hsurj v
  have hw := LinearMap.congr_fun hPA w
  simpa using sub_eq_zero.mpr hw

end Problem340

end

end OAI
