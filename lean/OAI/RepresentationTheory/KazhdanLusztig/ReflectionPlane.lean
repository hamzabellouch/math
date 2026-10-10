import Mathlib

namespace OAI

/-!
Linear reflection products and common root planes for nondegenerate ambient forms.
-/

section


namespace KLInvariance.ReflectionPlane
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- Independent linear forms give a surjection to the coordinate plane. -/
theorem formPair_surjective (f g : Module.Dual k V)
    (hfg : LinearIndependent k ![f, g]) : Function.Surjective (f.prod g) := by
  apply LinearMap.dualMap_injective_iff.mp
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro l hl
  change l = 0
  have hl' (v : V) : l (f v, g v) = 0 := LinearMap.congr_fun hl v
  have heval (c d : k) : l (c, d) = c * l (1, 0) + d * l (0, 1) := by
    have heq : (c, d) = c • ((1, 0) : k × k) + d • ((0, 1) : k × k) := by
      ext <;> simp
    rw [heq, map_add, map_smul, map_smul]
    rfl
  have hrel : l (1, 0) • f + l (0, 1) • g = 0 := by
    ext v
    change l (1, 0) * f v + l (0, 1) * g v = 0
    have hv := hl' v
    rw [heval] at hv
    simpa only [mul_comm] using hv
  obtain ⟨h₁, h₂⟩ := LinearIndependent.pair_iff.mp hfg _ _ hrel
  apply LinearMap.ext
  intro x
  obtain ⟨c, d⟩ := x
  change l (c, d) = 0
  rw [heval, h₁, h₂, mul_zero, mul_zero, add_zero]

/-- The range of the difference of a two-reflection product from the
identity is exactly the span of the two roots. -/
theorem range_preReflection_product_sub_id (α β : V) (f g : Module.Dual k V)
    (hfg : LinearIndependent k ![f, g]) :
    LinearMap.range ((Module.preReflection α f).comp (Module.preReflection β g) -
      LinearMap.id) = Submodule.span k {α, β} := by
  have hformula (v : V) :
      ((Module.preReflection α f).comp (Module.preReflection β g) -
        (LinearMap.id : V →ₗ[k] V)) v = (-f v + f β * g v) • α + (-g v) • β := by
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, Module.preReflection_apply,
      LinearMap.id_apply, map_sub, map_smul]
    module
  apply le_antisymm
  · rintro z ⟨v, rfl⟩
    rw [hformula]
    exact Submodule.mem_span_pair.mpr ⟨_, _, rfl⟩
  · intro z hz
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hz
    obtain ⟨v, hv⟩ := formPair_surjective f g hfg (-a - f β * b, -b)
    have hf : f v = -a - f β * b := congrArg Prod.fst hv
    have hg : g v = -b := congrArg Prod.snd hv
    refine ⟨v, ?_⟩
    rw [hformula, hf, hg]
    module


theorem range_reflection_product_sub_id
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate)
    (α β : V) (hα : B α α = 2) (hβ : B β β = 2)
    (hαβ : LinearIndependent k ![α, β]) :
    LinearMap.range (((Module.reflection hα).toLinearMap).comp
      (Module.reflection hβ).toLinearMap - LinearMap.id) = Submodule.span k {α, β} := by
  apply range_preReflection_product_sub_id
  have h := hαβ.map' B hB.ker_eq_bot
  have heq : (⇑B ∘ ![α, β]) = ![B α, B β] := by
    funext i
    fin_cases i <;> rfl
  rw [heq] at h
  exact h

/-- Equal products of two normalized reflections recover equal root
planes, the exact local geometric input to `dih:transport`. -/
theorem plane_eq_of_reflection_product_eq
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate)
    (α β γ δ : V)
    (hα : B α α = 2) (hβ : B β β = 2) (hγ : B γ γ = 2) (hδ : B δ δ = 2)
    (hαβ : LinearIndependent k ![α, β]) (hγδ : LinearIndependent k ![γ, δ])
    (heq : (Module.reflection hα).toLinearMap.comp (Module.reflection hβ).toLinearMap =
      (Module.reflection hγ).toLinearMap.comp (Module.reflection hδ).toLinearMap) :
    Submodule.span k {α, β} = Submodule.span k {γ, δ} := by
  rw [← range_reflection_product_sub_id B hB α β hα hβ hαβ,
    ← range_reflection_product_sub_id B hB γ δ hγ hδ hγδ, heq]

end KLInvariance.ReflectionPlane


end

end OAI
