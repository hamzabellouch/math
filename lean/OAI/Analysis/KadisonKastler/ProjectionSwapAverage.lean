import OAI.Analysis.KadisonKastler.InfiniteProjectionAveraging
import OAI.Analysis.KadisonKastler.FiniteProjectionAveraging

namespace OAI

/-! # Averaging a projection into half the identity by projection comparison -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- Orthogonal equivalent projections are exchanged by an ambient unitary. -/
theorem exists_unitary_swap_orthogonal_formula (v : PartialIsometry M)
    (ho : v.support.val * v.target.val = 0) :
    ∃ u : unitary (Algebra M),
      (u : Algebra M) * v.support.val * star (u : Algebra M) = v.target.val ∧
      (u : Algebra M) = v.val + star v.val + (1 - (v.support.val + v.target.val)) := by
  let p := v.support
  let q := v.target
  have hv : v.support = p := rfl
  have ht : v.target = q := rfl
  have hi : v.support.val * v.adjoint.support.val = 0 := by
    change v.support.val * v.target.val = 0
    rw [hv, ht]
    exact ho
  have hf : v.target.val * v.adjoint.target.val = 0 := by
    rw [PartialIsometry.adjoint_target, hv, ht]
    exact PartialIsometry.orthogonal_reverse p q ho
  let a := v.patch v.adjoint hi hf
  have hat : a.target = a.support := by
    apply Subtype.ext
    rw [PartialIsometry.patch_target, PartialIsometry.adjoint_target]
    change v.target.val + v.support.val = v.support.val + v.target.val
    exact add_comm _ _
  let c : AlgebraProjection M := ⟨1 - a.support.val, a.support.property.one_sub⟩
  have hac : a.support.val * (PartialIsometry.onProjection c).support.val = 0 :=
    a.support.property.mul_one_sub_self
  have hatc : a.target.val * (PartialIsometry.onProjection c).target.val = 0 := by
    rw [PartialIsometry.onProjection_target, hat]
    exact hac
  let z := a.patch (PartialIsometry.onProjection c) hac hatc
  have hzi : star z.val * z.val = 1 := by
    rw [z.initial]
    change a.support.val + (1 - a.support.val) = 1
    abel
  have hzt : z.val * star z.val = 1 := by
    change z.target.val = 1
    rw [PartialIsometry.patch_target, PartialIsometry.onProjection_target, hat]
    change a.support.val + (1 - a.support.val) = 1
    abel
  let u : unitary (Algebra M) := ⟨z.val, hzi, hzt⟩
  have hvz : v ≤ z := (v.le_patch v.adjoint hi hf).trans (a.le_patch _ hac hatc)
  have hup : (u : Algebra M) * p.val = v.val := by
    rw [← hv]
    exact hvz
  refine ⟨u, ?_, ?_⟩
  · calc
      (u : Algebra M) * p.val * star (u : Algebra M) =
        ((u : Algebra M) * p.val) * star ((u : Algebra M) * p.val) := by
          rw [star_mul, p.property.isSelfAdjoint.star_eq]
          calc
            _ = (u : Algebra M) * (p.val * p.val) * star (u : Algebra M) := by
              rw [p.property.isIdempotentElem.eq]
            _ = _ := by simp only [mul_assoc]
      _ = q.val := by rw [hup]; exact congrArg Subtype.val ht
  · rfl

/-- Orthogonal equivalence extends by the identity on the remaining space. -/
theorem exists_unitary_swap_orthogonal (p q : AlgebraProjection M)
    (ho : p.val * q.val = 0) (he : p.Equivalent q) :
    ∃ u : unitary (Algebra M), (u : Algebra M) * p.val * star (u : Algebra M) = q.val := by
  obtain ⟨v, hv, ht⟩ := he
  obtain ⟨u, hu, _⟩ := exists_unitary_swap_orthogonal_formula v (by rwa [hv, ht])
  exact ⟨u, by simpa only [hv, ht] using hu⟩

/-- A projection subequivalent to its complement can be averaged below one-half. -/
theorem exists_projection_half_average (p : AlgebraProjection M)
    (he : p.Subequivalent (⟨1 - p.val, p.property.one_sub⟩ : AlgebraProjection M)) :
    ∃ A : FiniteInnerAverage M,
      A.apply p.val.val ≤ (1 / 2 : ℂ) • (1 : H →L[ℂ] H) := by
  obtain ⟨v, hv, ht⟩ := he
  let q := v.target
  have ho : p.val * q.val = 0 := by
    change (1 - p.val) * q.val = q.val at ht
    rw [sub_mul, one_mul] at ht
    exact sub_eq_self.mp ht
  obtain ⟨u, hu⟩ := exists_unitary_swap_orthogonal p q ho ⟨v, hv, rfl⟩
  let A : FiniteInnerAverage M := {
    Index := Bool
    fintype := inferInstance
    nonempty := inferInstance
    unitary b := if b then u else 1 }
  have heq : A.apply p.val.val = (1 / 2 : ℂ) • (p.val.val + q.val.val) := by
    change (Fintype.card Bool : ℂ)⁻¹ •
      (∑ b : Bool, unitaryConj (ambientAlgebraUnitary (if b then u else 1)) p.val.val) = _
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hu' : unitaryConj (ambientAlgebraUnitary u) p.val.val = q.val.val :=
      congrArg Subtype.val hu
    rw [hu']
    have h1 : unitaryConj (ambientAlgebraUnitary (1 : unitary (Algebra M))) p.val.val = p.val.val := by
      change (1 : H →L[ℂ] H) * p.val.val * star (1 : H →L[ℂ] H) = _
      simp
    rw [h1, add_comm]
    norm_num
  refine ⟨A, ?_⟩
  rw [heq]
  have hs : p.val.val + q.val.val ≤ (1 : H →L[ℂ] H) := by
    have hpq := ambient_projection_le (show orthogonalSum p q ho ≤
        (⟨1, IsStarProjection.one _⟩ : AlgebraProjection M) from one_mul _)
    exact hpq
  have h := smul_le_smul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simpa only [← Complex.coe_smul, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] using h

end

end KadisonKastler

end OAI
