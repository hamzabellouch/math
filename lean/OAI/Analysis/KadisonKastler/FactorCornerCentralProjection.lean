import OAI.Analysis.KadisonKastler.MinimalProjectionEquivalence

namespace OAI

/-! # A central projection in a nonzero factor corner is trivial -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem factor_corner_central_projection (hM : ScalarCenter M)
    (p q : AlgebraProjection M) (hqp : q ≤ p)
    (hc : ∀ a : Algebra M, q.val * (p.val * a * p.val) =
      (p.val * a * p.val) * q.val) : q.val = 0 ∨ q = p := by
  classical
  by_cases hq : q.val = 0
  · exact Or.inl hq
  right
  by_contra hne
  let r := AlgebraProjection.remainder q p hqp
  have hr : r.val ≠ 0 := by
    intro h
    apply hne
    apply Subtype.ext
    exact (sub_eq_zero.mp h).symm
  have hf : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M) := by
    intro c h
    obtain ⟨z, hz⟩ := hM c.val c.property
      (fun a ha => congrArg Subtype.val (h ⟨a, ha⟩))
    exact ⟨z, Subtype.ext hz⟩
  obtain ⟨v, hvs, hvt, hv0⟩ :=
    traceFree_exists_nonzero_partialIsometry_between_projections hf q r hq hr
  have hvq : v.val * q.val = v.val := (v.support_le_iff_mul q).mp hvs
  have hrv : r.val * v.val = v.val := (v.target_le_iff_mul r).mp hvt
  have hpr : p.val * r.val = r.val := AlgebraProjection.remainder_le q p hqp
  have hqp' : q.val * p.val = q.val := projection_mul_of_le hqp
  have hpv : p.val * v.val = v.val := by
    calc
      _ = p.val * (r.val * v.val) := by rw [hrv]
      _ = v.val := by rw [← mul_assoc, hpr, hrv]
  have hvp : v.val * p.val = v.val := by
    calc
      _ = (v.val * q.val) * p.val := by rw [hvq]
      _ = v.val := by rw [mul_assoc, hqp', hvq]
  have hqr : q.val * r.val = 0 := by
    change q.val * (p.val - q.val) = 0
    rw [mul_sub, hqp', q.property.isIdempotentElem.eq, sub_self]
  have hqv : q.val * v.val = 0 := by
    calc
      _ = q.val * (r.val * v.val) := by rw [hrv]
      _ = 0 := by rw [← mul_assoc, hqr, zero_mul]
  have hh := hc v.val
  rw [hpv, hvp, hqv, hvq] at hh
  apply hv0
  rw [← v.initial, ← hh, star_zero, zero_mul]

end

end KadisonKastler

end OAI
