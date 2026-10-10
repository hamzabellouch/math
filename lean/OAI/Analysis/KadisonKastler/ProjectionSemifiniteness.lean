import OAI.Analysis.KadisonKastler.PublishedProperInfiniteProjection
import OAI.Analysis.FactorGeneration.DyadicComparison

namespace OAI

/-! # Projection semifiniteness from one finite projection in a factor

This is the projection-theoretic step needed after constructing a finite
frequency window in the modular core.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem finiteProjectionIn_of_le {p q : AlgebraProjection M}
    (hp : FiniteProjectionIn M p.val) (hqp : q ≤ p) : FiniteProjectionIn M q.val := by
  intro v hvi hqv
  let V : PartialIsometry M := ⟨q, v, hvi⟩
  let r := AlgebraProjection.remainder q p hqp
  have hvq : v * q.val = v := V.mul_support
  have hqp' : q.val * p.val = q.val := by
    have h := congrArg star hqp
    simpa only [star_mul, p.property.isSelfAdjoint.star_eq,
      q.property.isSelfAdjoint.star_eq] using h
  have hpv : p.val * v = v := by
    calc
      p.val * v = p.val * (q.val * v) := by rw [hqv]
      _ = v := by rw [← mul_assoc, hqp, hqv]
  have hvp : v * p.val = v := by
    calc
      v * p.val = (v * q.val) * p.val := by rw [hvq]
      _ = v := by rw [mul_assoc, hqp', hvq]
  have hrv : r.val * v = 0 := by
    change (p.val - q.val) * v = 0
    rw [sub_mul, hpv, hqv, sub_self]
  have hvr : v * r.val = 0 := by
    change v * (p.val - q.val) = 0
    rw [mul_sub, hvp, hvq, sub_self]
  have hsvr : star v * r.val = 0 := by
    simpa only [star_mul, r.property.isSelfAdjoint.star_eq, star_zero]
      using congrArg star hrv
  have hrsv : r.val * star v = 0 := by
    simpa only [star_mul, r.property.isSelfAdjoint.star_eq, star_zero]
      using congrArg star hvr
  have hsum : q.val + r.val = p.val := by
    change q.val + (p.val - q.val) = p.val
    abel
  have hw : star (v + r.val) * (v + r.val) = p.val := by
    rw [star_add, r.property.isSelfAdjoint.star_eq, add_mul, mul_add, mul_add,
      hvi, hsvr, hrv, r.property.isIdempotentElem.eq, add_zero, zero_add, hsum]
  have hleft : p.val * (v + r.val) = v + r.val := by
    rw [mul_add, hpv, show p.val * r.val = r.val from AlgebraProjection.remainder_le q p hqp]
  have hfinal := hp (v + r.val) hw hleft
  have hs : v * star v + r.val = p.val := by
    simpa only [star_add, r.property.isSelfAdjoint.star_eq, add_mul, mul_add,
      hvr, hrsv, r.property.isIdempotentElem.eq, add_zero, zero_add] using hfinal
  calc
    v * star v = (v * star v + r.val) - r.val := by abel
    _ = p.val - r.val := by rw [hs]
    _ = q.val := by change p.val - (p.val - q.val) = q.val; abel

theorem projectionSemifinite_of_finite_projection (hM : ScalarCenter M)
    (p : AlgebraProjection M) (hp0 : p.val ≠ 0) (hp : FiniteProjectionIn M p.val) :
    ∀ q : AlgebraProjection M, q.val ≠ 0 →
      ∃ r : AlgebraProjection M, r ≤ q ∧ r.val ≠ 0 ∧ FiniteProjectionIn M r.val := by
  have hf : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M) := by
    intro c hc
    obtain ⟨z, hz⟩ := hM c.val c.property
      (fun a ha => congrArg Subtype.val (hc ⟨a, ha⟩))
    exact ⟨z, Subtype.ext hz⟩
  intro q hq
  obtain ⟨v, hvs, hvt, hv0⟩ :=
    traceFree_exists_nonzero_partialIsometry_between_projections hf p q hp0 hq
  have hfinite := finiteProjectionIn_of_le hp hvs
  refine ⟨v.target, hvt, ?_, finiteProjectionIn_of_equivalent
    v.support v.target hfinite v.val v.initial rfl⟩
  intro hz
  have hvnorm : ‖v.val‖ = 0 := by
    have hh := congrArg norm hz
    simp only [norm_zero] at hh
    change ‖v.val * star v.val‖ = 0 at hh
    rw [CStarRing.norm_self_mul_star] at hh
    nlinarith [norm_nonneg v.val]
  have hvzero := norm_eq_zero.mp hvnorm
  apply hv0
  calc
    v.support.val = star v.val * v.val := v.initial.symm
    _ = 0 := by rw [hvzero, star_zero, zero_mul]

end

end KadisonKastler

end OAI
