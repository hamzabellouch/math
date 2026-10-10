import OAI.Analysis.KadisonKastler.CentralProjectionComparison

namespace OAI

/-! # Central bounds for a two-unitary projection average -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- Swapping the matched parts fixes every projection orthogonal to both. -/
theorem swap_formula_fixes_projection (v : PartialIsometry M)
    (u : unitary (Algebra M))
    (hu : (u : Algebra M) = v.val + star v.val + (1 - (v.support.val + v.target.val)))
    (r : AlgebraProjection M)
    (hr : v.support.val * r.val = 0) (ht : v.target.val * r.val = 0) :
    (u : Algebra M) * r.val * star (u : Algebra M) = r.val := by
  have hvr : v.val * r.val = 0 := v.mul_eq_zero (PartialIsometry.onProjection r)
    (by simpa only [PartialIsometry.onProjection_target] using hr)
  have hsr : star v.val * r.val = 0 :=
    v.adjoint.mul_eq_zero (PartialIsometry.onProjection r)
      (by
        rw [PartialIsometry.onProjection_target]
        change v.target.val * r.val = 0
        exact ht)
  have hur : (u : Algebra M) * r.val = r.val := by
    rw [hu, add_mul, add_mul, hvr, hsr, zero_add, sub_mul, one_mul, add_mul, hr, ht]
    simp
  calc
    (u : Algebra M) * r.val * star (u : Algebra M) =
        ((u : Algebra M) * r.val) * star ((u : Algebra M) * r.val) := by
      rw [star_mul, r.property.isSelfAdjoint.star_eq]
      calc
        _ = (u : Algebra M) * (r.val * r.val) * star (u : Algebra M) := by
          rw [r.property.isIdempotentElem.eq]
        _ = _ := by simp only [mul_assoc]
    _ = r.val := by rw [hur, r.property.isSelfAdjoint.star_eq, r.property.isIdempotentElem.eq]

/-- Matched positive and negative spectral parts give complementary upper
bounds measured by one central projection. -/
theorem exists_central_projection_average (p : AlgebraProjection M) :
    ∃ (A : FiniteInnerAverage M) (z : AlgebraProjection M),
      (∀ a : Algebra M, a * z.val = z.val * a) ∧
      A.apply p.val.val ≤ (1 / 2 : ℝ) • (1 + z.val.val) ∧
      A.apply (1 - p.val.val) ≤ (1 / 2 : ℝ) • (2 • (1 : H →L[ℂ] H) - z.val.val) := by
  let q : AlgebraProjection M := ⟨1 - p.val, p.property.one_sub⟩
  obtain ⟨v, hp, hq, z, hz, hrz, hsz⟩ := exists_centrally_separated_comparison p q
  let r := AlgebraProjection.remainder v.support p hp
  let s := AlgebraProjection.remainder v.target q hq
  have hpq : p.val * q.val = 0 := p.property.mul_one_sub_self
  have ho : v.support.val * v.target.val = 0 :=
    projection_orthogonal_of_le hpq hp hq
  obtain ⟨u, hu, huf⟩ := exists_unitary_swap_orthogonal_formula v ho
  have hvr : v.support.val * r.val = 0 := AlgebraProjection.remainder_orthogonal _ _ hp
  have htr : v.target.val * r.val = 0 := projection_orthogonal_of_le
    (PartialIsometry.orthogonal_reverse p q hpq) hq (AlgebraProjection.remainder_le _ _ hp)
  have hur := swap_formula_fixes_projection v u huf r hvr htr
  have hup : (u : Algebra M) * p.val * star (u : Algebra M) = v.target.val + r.val := by
    have he : p.val = v.support.val + r.val := by
      change p.val = v.support.val + (p.val - v.support.val)
      abel
    rw [he, mul_add, add_mul, hu, hur]
  let A : FiniteInnerAverage M := {
    Index := Bool
    fintype := inferInstance
    nonempty := inferInstance
    unitary b := if b then u else 1 }
  have hA : A.apply p.val.val = (1 / 2 : ℝ) • (1 + r.val.val - s.val.val) := by
    change (Fintype.card Bool : ℂ)⁻¹ •
      (∑ b : Bool, unitaryConj (ambientAlgebraUnitary (if b then u else 1)) p.val.val) = _
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hu' : unitaryConj (ambientAlgebraUnitary u) p.val.val = v.target.val.val + r.val.val :=
      congrArg Subtype.val hup
    rw [hu']
    have h1 : unitaryConj (ambientAlgebraUnitary (1 : unitary (Algebra M))) p.val.val = p.val.val := by
      change (1 : H →L[ℂ] H) * p.val.val * star (1 : H →L[ℂ] H) = _
      simp
    rw [h1]
    have he : v.target.val.val + r.val.val + p.val.val = 1 + r.val.val - s.val.val := by
      change v.target.val.val + r.val.val + p.val.val =
        1 + r.val.val - ((1 - p.val.val) - v.target.val.val)
      abel
    rw [he]
    rw [← Complex.coe_smul]
    norm_num
  have hB : A.apply (1 - p.val.val) = (1 / 2 : ℝ) • (1 - r.val.val + s.val.val) := by
    rw [A.apply_sub, show A.apply 1 = 1 by simpa using A.apply_scalar 1, hA]
    module
  have hr0 : (0 : H →L[ℂ] H) ≤ r.val.val :=
    (r.property.map M.toStarSubalgebra.subtype).nonneg
  have hs0 : (0 : H →L[ℂ] H) ≤ s.val.val :=
    (s.property.map M.toStarSubalgebra.subtype).nonneg
  have hr : r.val.val ≤ z.val.val := ambient_projection_le hrz
  have hs : s.val.val ≤ 1 - z.val.val := ambient_projection_le hsz
  refine ⟨A, z, hz, ?_, ?_⟩
  · rw [hA]
    apply smul_le_smul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    exact (sub_le_self _ hs0).trans (add_le_add le_rfl hr)
  · rw [hB]
    apply smul_le_smul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have h := add_le_add (sub_le_self (1 : H →L[ℂ] H) hr0) hs
    convert h using 1; module

end

end KadisonKastler

end OAI
