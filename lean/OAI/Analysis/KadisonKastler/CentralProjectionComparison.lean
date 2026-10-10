import OAI.Analysis.KadisonKastler.ProjectionSwapAverage

namespace OAI

/-! # Central separation of the remainders in projection comparison -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- A maximal partial isometry leaves no algebraic link between its two
remainder projections. This statement does not require scalar center. -/
theorem exists_partialIsometry_separated_remainders (p q : AlgebraProjection M) :
    ∃ (v : PartialIsometry M) (hp : v.support ≤ p) (hq : v.target ≤ q),
      ∀ a : Algebra M,
        (AlgebraProjection.remainder v.target q hq).val * a *
          (AlgebraProjection.remainder v.support p hp).val = 0 := by
  obtain ⟨v, hp, hq, hmax⟩ := PartialIsometry.traceFree_exists_maximal_between p q
  refine ⟨v, hp, hq, ?_⟩
  let r := AlgebraProjection.remainder v.support p hp
  let s := AlgebraProjection.remainder v.target q hq
  intro a
  by_contra ha
  obtain ⟨w, hwr, hws, hw0⟩ := exists_partialIsometry_of_link r s (s.val * a * r.val)
    (by rw [mul_assoc, r.property.isIdempotentElem.eq])
    (by rw [← mul_assoc, ← mul_assoc, s.property.isIdempotentElem.eq]) ha
  have hpw : v.support.val * w.support.val = 0 := by
    calc
      _ = v.support.val * (r.val * w.support.val) := by rw [hwr]
      _ = (v.support.val * r.val) * w.support.val := (mul_assoc _ _ _).symm
      _ = 0 := by rw [AlgebraProjection.remainder_orthogonal, zero_mul]
  have hqw : v.target.val * w.target.val = 0 := by
    calc
      _ = v.target.val * (s.val * w.target.val) := by rw [hws]
      _ = (v.target.val * s.val) * w.target.val := (mul_assoc _ _ _).symm
      _ = 0 := by rw [AlgebraProjection.remainder_orthogonal, zero_mul]
  let u := v.patch w hpw hqw
  have hup : u.support ≤ p := by
    change p.val * (v.support.val + w.support.val) = v.support.val + w.support.val
    rw [mul_add, hp, show p.val * w.support.val = w.support.val from
      hwr.trans (AlgebraProjection.remainder_le _ _ hp)]
  have huq : u.target ≤ q := by
    apply (u.target_le_iff_mul q).mpr
    change q.val * (v.val + w.val) = v.val + w.val
    rw [mul_add, (v.target_le_iff_mul q).mp hq,
      (w.target_le_iff_mul q).mp (hws.trans (AlgebraProjection.remainder_le _ _ hq))]
  have hvu : v ≤ u := v.le_patch w hpw hqw
  exact (v.patch_ne w hpw hqw hw0) (le_antisymm (hmax u hup huq hvu) hvu)

/-- One central projection separates the two unmatched remainders. -/
theorem exists_centrally_separated_comparison (p q : AlgebraProjection M) :
    ∃ (v : PartialIsometry M) (hp : v.support ≤ p) (hq : v.target ≤ q)
      (z : AlgebraProjection M),
      (∀ a : Algebra M, a * z.val = z.val * a) ∧
      AlgebraProjection.remainder v.support p hp ≤ z ∧
      AlgebraProjection.remainder v.target q hq ≤
        (⟨1 - z.val, z.property.one_sub⟩ : AlgebraProjection M) := by
  obtain ⟨v, hp, hq, hlink⟩ := exists_partialIsometry_separated_remainders p q
  let r := AlgebraProjection.remainder v.support p hp
  let s := AlgebraProjection.remainder v.target q hq
  let z := centralSupport r
  refine ⟨v, hp, hq, z, centralSupport_commutes r, le_centralSupport r, ?_⟩
  have hz : s.val * z.val = 0 := mul_centralSupport_eq_zero_of_no_links r s hlink
  have hz' : z.val * s.val = 0 := PartialIsometry.orthogonal_reverse s z hz
  change (1 - z.val) * s.val = s.val
  rw [sub_mul, one_mul, hz', sub_zero]

end

end KadisonKastler

end OAI
