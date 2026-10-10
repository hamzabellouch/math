import OAI.Analysis.KadisonKastler.PublishedTypeIInjectivity
import OAI.Analysis.KadisonKastler.ProjectionSemifiniteness
import OAI.Analysis.KadisonKastler.SemifiniteIsomorphism

namespace OAI

/-! # Minimal projections, equivalence and automorphisms in a factor -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem partialIsometry_target_ne_zero (v : PartialIsometry M)
    (h : v.support.val ≠ 0) : v.target.val ≠ 0 := by
  intro hz
  have hv : v.val = 0 := by
    have hh := v.target_mul
    rw [hz, zero_mul] at hh
    exact hh.symm
  apply h
  rw [← v.initial, hv, star_zero, zero_mul]

theorem minimalProjection_partialIsometry_target (v : PartialIsometry M)
    (hp : IsMinimalProjectionIn M v.support) : IsMinimalProjectionIn M v.target := by
  refine ⟨partialIsometry_target_ne_zero v hp.1, ?_⟩
  intro q hq
  have hqright : q.val * v.target.val = q.val := projection_mul_of_le hq
  have hvstar : v.support.val * star v.val = star v.val := by
    simpa only [star_mul, v.support.property.isSelfAdjoint.star_eq, star_star] using
      congrArg star v.mul_support
  let a : Algebra M := star v.val * q.val * v.val
  have has : IsSelfAdjoint a := by
    change star (star v.val * q.val * v.val) = star v.val * q.val * v.val
    simp only [star_mul, star_star, q.property.isSelfAdjoint.star_eq, mul_assoc]
  have hai : a * a = a := by
    change (star v.val * q.val * v.val) * (star v.val * q.val * v.val) = _
    calc
      _ = star v.val * (q.val * v.target.val) * q.val * v.val := by
        change _ = star v.val * (q.val * (v.val * star v.val)) * q.val * v.val
        simp only [mul_assoc]
      _ = a := by rw [hqright]; simp only [a, mul_assoc, q.property.isIdempotentElem.eq]
  let r : AlgebraProjection M := ⟨a, ⟨hai, has⟩⟩
  have hr : r ≤ v.support := by
    change v.support.val * (star v.val * q.val * v.val) = star v.val * q.val * v.val
    simp only [← mul_assoc, hvstar]
  have hrecover : v.val * r.val * star v.val = q.val := by
    change v.val * (star v.val * q.val * v.val) * star v.val = q.val
    calc
      _ = v.target.val * q.val * v.target.val := by
        change _ = (v.val * star v.val) * q.val * (v.val * star v.val)
        simp only [mul_assoc]
      _ = q.val := by rw [show v.target.val * q.val = q.val from hq, hqright]
  rcases hp.2 r hr with hz | he
  · left
    rw [hz, mul_zero, zero_mul] at hrecover
    exact hrecover.symm
  · right
    apply Subtype.ext
    rw [he, v.mul_support] at hrecover
    exact hrecover.symm

theorem minimalProjection_map (e : Algebra M ≃⋆ₐ[ℂ] Algebra M)
    (p : AlgebraProjection M) (hp : IsMinimalProjectionIn M p) :
    IsMinimalProjectionIn M (mapAlgebraProjection e p) := by
  refine ⟨map_ne_zero e hp.1, ?_⟩
  intro q hq
  let r := mapAlgebraProjection e.symm q
  have hr : r ≤ p := by
    apply e.injective
    change e (p.val * e.symm q.val) = e (e.symm q.val)
    rw [map_mul, e.apply_symm_apply]
    exact hq
  rcases hp.2 r hr with hz | he
  · left
    have hh := congrArg e hz
    simpa only [r, mapAlgebraProjection, e.apply_symm_apply, map_zero] using hh
  · right
    apply Subtype.ext
    have hh := congrArg (fun s : AlgebraProjection M => e s.val) he
    simpa only [r, mapAlgebraProjection, e.apply_symm_apply] using hh

private theorem factor_scalar_algebra (hM : ScalarCenter M) :
    ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M) := by
  intro c hc
  obtain ⟨z, hz⟩ := hM c.val c.property
    (fun a ha => congrArg Subtype.val (hc ⟨a, ha⟩))
  exact ⟨z, Subtype.ext hz⟩

theorem factor_exists_minimal_below (hM : ScalarCenter M)
    (p : AlgebraProjection M) (hp : IsMinimalProjectionIn M p)
    (q : AlgebraProjection M) (hq : q.val ≠ 0) :
    ∃ r : AlgebraProjection M, r ≤ q ∧ IsMinimalProjectionIn M r := by
  obtain ⟨v, hvs, hvt, hv0⟩ :=
    traceFree_exists_nonzero_partialIsometry_between_projections
      (factor_scalar_algebra hM) p q hp.1 hq
  have hvp : v.support = p := (hp.2 v.support hvs).resolve_left hv0
  exact ⟨v.target, hvt, minimalProjection_partialIsometry_target v (hvp ▸ hp)⟩

theorem factor_minimal_projections_equivalent (hM : ScalarCenter M)
    (p q : AlgebraProjection M) (hp : IsMinimalProjectionIn M p)
    (hq : IsMinimalProjectionIn M q) : p.Equivalent q := by
  obtain ⟨v, hvs, hvt, hv0⟩ :=
    traceFree_exists_nonzero_partialIsometry_between_projections
      (factor_scalar_algebra hM) p q hp.1 hq.1
  exact ⟨v, (hp.2 v.support hvs).resolve_left hv0,
    (hq.2 v.target hvt).resolve_left (partialIsometry_target_ne_zero v hv0)⟩

end

end KadisonKastler

end OAI
