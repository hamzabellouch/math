import OAI.Analysis.StrictMeans.GridSupport

namespace OAI

section
namespace StrictInverseFirstPower
open LinearMap Module

lemma finite_euler_inequality {K V₀ V₁ V₂ : Type*} [Field K]
    [AddCommGroup V₀] [Module K V₀] [FiniteDimensional K V₀]
    [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁]
    [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂]
    (d₁ : V₁ →ₗ[K] V₀) (d₂ : V₂ →ₗ[K] V₁) (aug : V₀ →ₗ[K] K)
    (hinj : Function.Injective d₂) (hexact : d₂.range = d₁.ker)
    (haug : aug ∘ₗ d₁ = 0) (hne : aug ≠ 0) :
    finrank K V₁ + 1 ≤ finrank K V₀ + finrank K V₂ := by
  have hr := d₁.finrank_range_add_finrank_ker
  have hd : finrank K d₁.ker = finrank K V₂ := by
    rw [← hexact]
    exact LinearMap.finrank_range_of_inj hinj
  have hle : d₁.range ≤ aug.ker := LinearMap.range_le_ker_iff.mpr haug
  have hh : aug.ker < ⊤ := lt_top_iff_ne_top.mpr (by simpa using hne)
  have ht := Submodule.finrank_lt_finrank_of_lt hh
  have hm := Submodule.finrank_mono hle
  simp only [finrank_top] at ht
  omega

end StrictInverseFirstPower

end

end OAI
