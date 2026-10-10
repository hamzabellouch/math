import OAI.Analysis.KadisonKastler.FactorIsomorphism

namespace OAI

/-! # Transport of semifinite factor type under a star isomorphism -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

def mapAlgebraProjection (e : Algebra M ≃⋆ₐ[ℂ] Algebra N) (p : AlgebraProjection M) :
    AlgebraProjection N := ⟨e p.val, p.property.map e⟩

theorem mapAlgebraProjection_mono (e : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    {p q : AlgebraProjection M} (hpq : p ≤ q) :
    mapAlgebraProjection e p ≤ mapAlgebraProjection e q := by
  change e q.val * e p.val = e p.val
  rw [← map_mul]
  exact congrArg e hpq

theorem map_ne_zero (e : Algebra M ≃⋆ₐ[ℂ] Algebra N) {x : Algebra M} (hx : x ≠ 0) :
    e x ≠ 0 := by
  intro h
  apply hx
  apply e.injective
  rwa [map_zero]

theorem TypeIIInfinityFactor.of_starAlgEquiv (hM : TypeIIInfinityFactor M)
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra N) : TypeIIInfinityFactor N where
  factor := hM.factor.of_starAlgEquiv e
  properlyInfinite := hM.properlyInfinite.of_starAlgEquiv e
  semifinite := by
    intro p hp
    let p₀ := mapAlgebraProjection e.symm p
    have hp₀ : p₀.val ≠ 0 := map_ne_zero e.symm hp
    obtain ⟨q, hqp, hq, hqf⟩ := hM.semifinite p₀ hp₀
    refine ⟨mapAlgebraProjection e q, ?_, map_ne_zero e hq, ?_⟩
    · have h := mapAlgebraProjection_mono e hqp
      change e p₀.val * e q.val = e q.val at h
      change p.val * e q.val = e q.val
      simpa only [p₀, mapAlgebraProjection, e.apply_symm_apply] using h
    · exact FiniteProjectionIn.of_starAlgEquiv e q.val hqf
  diffuse := by
    intro p hp hp0
    obtain ⟨q, hq, hq0, hqp, hpq, hqp'⟩ :=
      hM.diffuse (e.symm p) (hp.map e.symm) (map_ne_zero e.symm hp0)
    refine ⟨e q, hq.map e, map_ne_zero e hq0, ?_, ?_, ?_⟩
    · intro he
      apply hqp
      have hh := congrArg e.symm he
      rw [e.symm_apply_apply] at hh
      exact hh
    · have h := congrArg e hpq
      rw [map_mul, e.apply_symm_apply] at h
      exact h
    · have h := congrArg e hqp'
      rw [map_mul, e.apply_symm_apply] at h
      exact h

end

end KadisonKastler

end OAI
