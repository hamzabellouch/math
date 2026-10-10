import OAI.Analysis.IrrationalRotation.Operators.AffiliatedTransport
import OAI.Analysis.IrrationalRotation.Analysis.UnboundedMultiplier

namespace OAI

noncomputable section

namespace Invariant233.WeightedShift

open InvariantRotation.AffiliatedTransport

theorem transported_invariant_weightedShift
    (h : ℤ → ℂ) (f g : Weight) (c : ℂ) (hc : c ≠ 0)
    (hfg : ∀ k : ℤ, h (k + 1) * f k = c * g k * h k)
    (p : Submodule ℂ Hilbert)
    (hp : ∀ x ∈ p, operator f x ∈ p) :
    ∀ y ∈ transported (unboundedMultiplier h) p,
      operator g y ∈ transported (unboundedMultiplier h) p := by
  have hD : ∀ x ∈ (unboundedMultiplier h).domain,
      operator f x ∈ (unboundedMultiplier h).domain := by
    intro x hx
    exact operator_mem_multiplierDomain h f g c hfg ⟨x, hx⟩
  have hAB : ∀ x : (unboundedMultiplier h).domain,
      unboundedMultiplier h ⟨operator f x, hD x x.property⟩ =
        (c • operator g) (unboundedMultiplier h x) := by
    intro x
    exact multiplier_intertwines h f g c hfg x
  have hinv := transported_invariant (unboundedMultiplier h) p
    (operator f) (c • operator g) hp hD hAB
  intro y hy
  have hmem := (transported (unboundedMultiplier h) p).smul_mem c⁻¹ (hinv y hy)
  simpa only [smul_apply, smul_smul, inv_mul_cancel₀ hc,
    one_smul] using hmem

theorem transported_projection_invariant_weightedShift
    (h : ℤ → ℂ) (f g : Weight) (c : ℂ) (hc : c ≠ 0)
    (hfg : ∀ k : ℤ, h (k + 1) * f k = c * g k * h k)
    (p : Submodule ℂ Hilbert)
    (hp : ∀ x ∈ p, operator f x ∈ p) :
    let P := (transported (unboundedMultiplier h) p).starProjection
    (1 - P) * operator g * P = 0 := by
  let S := transported (unboundedMultiplier h) p
  have hinv : S ∈ Module.End.invtSubmodule (operator g).toLinearMap :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mpr
      (transported_invariant_weightedShift h f g c hc hfg p hp)
  have hrange : S.starProjection.range ∈
      Module.End.invtSubmodule (operator g).toLinearMap := by
    simpa only [Submodule.range_starProjection] using hinv
  have heq := (ContinuousLinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff
    S.isIdempotentElem_starProjection).mp hrange
  change S.starProjection * operator g * S.starProjection =
    operator g * S.starProjection at heq
  change (1 - S.starProjection) * operator g * S.starProjection = 0
  rw [sub_mul, one_mul, sub_mul, heq, sub_self]

theorem exponential_inverse_transported_orthogonal
    (b : ℤ → ℝ) (p : Submodule ℂ Hilbert) :
    transported (unboundedMultiplier (fun k => (Real.exp (b k) : ℂ))).inverse pᗮ ≤
      (transported (unboundedMultiplier (fun k => (Real.exp (b k) : ℂ))) p)ᗮ := by
  apply inverse_transported_le_orthogonal_of_selfAdjoint
  · exact isSelfAdjoint_unboundedMultiplier_real (fun k => Real.exp (b k))
  · exact LinearMap.ker_eq_bot.mpr (exponential_multiplier_injective b)

end Invariant233.WeightedShift

end

end OAI
