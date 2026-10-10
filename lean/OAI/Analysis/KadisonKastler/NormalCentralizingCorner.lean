import OAI.Analysis.KadisonKastler.CoreFixedCornerObstruction
import OAI.Analysis.KadisonKastler.NormalCoreIsomorphism
import OAI.Analysis.KadisonKastler.FactorIsomorphism

namespace OAI

/-! # Normal change of state to a pointwise fixed corner -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace H] [TopologicalSpace.SeparableSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

theorem regularCore_not_factor_of_normal_centralizing_corner
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    (he : BoundedWeakNormal M (N.toStarSubalgebra.subtype.comp e.toStarAlgHom))
    (Ω : H) (ξ : K)
    (hΩs : Function.Injective (algebraVectorMap M Ω))
    (hΩc : DenseRange (algebraVectorMap M Ω))
    (hξs : Function.Injective (algebraVectorMap N ξ))
    (hξc : DenseRange (algebraVectorMap N ξ))
    (p : AlgebraProjection M) (hp : p.val ≠ 0)
    (hc : ∀ a : Algebra M, ProductStateCentralizes N ξ (e (p.val * a * p.val)).val)
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (hn : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (hm : IsModularStateGroup M Ω U) : ¬ ScalarCenter (regularCoreAlgebra U hU M) := by
  obtain ⟨_, m⟩ := (publishedModularSpectralResolution K N ξ hξc hξs).some
  have hnN : ∀ t a, a ∈ N → unitaryConj (m.group t) a ∈ N := by
    intro t a ha
    change unitaryConj (m.group t) a ∈ (N : Set (K →L[ℂ] K))
    rw [← m.normalizes t]
    exact Set.mem_image_of_mem _ ha
  let q := mapAlgebraProjection e p
  have hq : q.val ≠ 0 := map_ne_zero e hp
  have hfix : ∀ t a, a ∈ N → unitaryConj (m.group t) (q.val.val * a * q.val.val) =
      q.val.val * a * q.val.val := by
    intro t a ha
    let b := e.symm ⟨a, ha⟩
    have hab : e b = ⟨a, ha⟩ := e.apply_symm_apply ⟨a, ha⟩
    have hx : (e (p.val * b * p.val)).val = q.val.val * a * q.val.val := by
      have hmul : e (p.val * b * p.val) = e p.val * e b * e p.val := by
        rw [map_mul, map_mul]
      rw [hmul, hab]
      rfl
    rw [← hx]
    exact m.centralizer_fixed _ (e (p.val * b * p.val)).property (hc b) t
  obtain ⟨E⟩ := modularCore_equiv_of_normal e he Ω ξ hΩc hξc hΩs hξs
    U hU hn hm m.group m.continuous hnN m.isModular
  intro hf
  exact regularCore_not_factor_of_fixed_corner m.group m.continuous N hnN q hq hfix
    (hf.of_starAlgEquiv E)

end

end KadisonKastler

end OAI
