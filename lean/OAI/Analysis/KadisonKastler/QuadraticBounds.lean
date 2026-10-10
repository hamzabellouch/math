import OAI.Analysis.KadisonKastler.Algebra
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# Extracting a commutator bound from quadratic forms

This is the final operator-norm step of the randomized amplification
argument in §3. The scalar recovery estimate is kept explicit.
-/

namespace KadisonKastler

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_le_of_selfAdjoint_quadratic (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    {C : ℝ} (hC : 0 ≤ C)
    (hquad : ∀ x : H, |(inner ℂ (T x) x).re| ≤ C * ‖x‖ ^ 2) :
    ‖T‖ ≤ C := by
  rw [T.norm_eq_iSup_rayleighQuotient hT.isSymmetric]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · simpa [hx] using hC
  · have hxpos : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
    change |(inner ℂ (T x) x).re / ‖x‖ ^ 2| ≤ C
    rw [abs_div, abs_of_pos hxpos]
    exact (div_le_iff₀ hxpos).mpr (hquad x)

/-- A unit-sphere quadratic estimate suffices for the full operator norm. -/
theorem norm_le_of_unit_selfAdjoint_quadratic (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    {C : ℝ} (hC : 0 ≤ C)
    (hquad : ∀ x : H, ‖x‖ = 1 → |(inner ℂ (T x) x).re| ≤ C) :
    ‖T‖ ≤ C := by
  rw [T.norm_eq_iSup_rayleighQuotient hT.isSymmetric]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · simpa only [hx, ContinuousLinearMap.rayleighQuotient_apply_zero, abs_zero] using hC
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    let c : ℂ := ((‖x‖⁻¹ : ℝ) : ℂ)
    have hc : c ≠ 0 := by
      change ((‖x‖⁻¹ : ℝ) : ℂ) ≠ 0
      exact_mod_cast inv_ne_zero hn
    have hy : ‖c • x‖ = 1 := by
      rw [norm_smul]
      simp only [c, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
        inv_mul_cancel₀ hn]
    have he := T.rayleigh_smul x hc
    rw [← he]
    change |(inner ℂ (T (c • x)) (c • x)).re / ‖c • x‖ ^ 2| ≤ C
    rw [hy, one_pow, div_one]
    exact hquad (c • x) hy

/-- A bound on the difference of a selfadjoint quadratic form before and
after a unitary gives the same bound on its commutator with the unitary. -/
theorem norm_commutator_le_of_quadratic (h : H →L[ℂ] H) (hh : IsSelfAdjoint h)
    (u : unitary (H →L[ℂ] H)) {C : ℝ} (hC : 0 ≤ C)
    (hquad : ∀ x : H,
      |(inner ℂ (h x) x).re - (inner ℂ (h ((u : H →L[ℂ] H) x))
          ((u : H →L[ℂ] H) x)).re| ≤ C * ‖x‖ ^ 2) :
    ‖h * (u : H →L[ℂ] H) - (u : H →L[ℂ] H) * h‖ ≤ C := by
  let D := h - star (u : H →L[ℂ] H) * h * (u : H →L[ℂ] H)
  have hD : IsSelfAdjoint D := by
    change star D = D
    simp only [D, star_sub, star_mul, star_star, hh.star_eq, mul_assoc]
  have hnorm : ‖D‖ ≤ C := norm_le_of_selfAdjoint_quadratic D hD hC (by
    intro x
    simpa only [D, sub_apply, inner_sub_left, Complex.sub_re,
      mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left] using hquad x)
  have heq : h * (u : H →L[ℂ] H) - (u : H →L[ℂ] H) * h =
      -(u : H →L[ℂ] H) * D := by
    have hu : (u : H →L[ℂ] H) * star (u : H →L[ℂ] H) = 1 :=
      Unitary.mul_star_self_of_mem u.property
    symm
    calc
      _ = ((u : H →L[ℂ] H) * star (u : H →L[ℂ] H)) * h *
          (u : H →L[ℂ] H) - (u : H →L[ℂ] H) * h := by
        dsimp [D]
        noncomm_ring
      _ = _ := by rw [hu, one_mul]
  rw [heq, neg_mul, norm_neg, CStarRing.norm_coe_unitary_mul]
  exact hnorm

/-- The unit-sphere version used after the randomized-row estimate. -/
theorem norm_commutator_le_of_unit_quadratic (h : H →L[ℂ] H) (hh : IsSelfAdjoint h)
    (u : unitary (H →L[ℂ] H)) {C : ℝ} (hC : 0 ≤ C)
    (hquad : ∀ x : H, ‖x‖ = 1 →
      |(inner ℂ (h x) x).re - (inner ℂ (h ((u : H →L[ℂ] H) x))
        ((u : H →L[ℂ] H) x)).re| ≤ C) :
    ‖h * (u : H →L[ℂ] H) - (u : H →L[ℂ] H) * h‖ ≤ C := by
  let D := h - star (u : H →L[ℂ] H) * h * (u : H →L[ℂ] H)
  have hD : IsSelfAdjoint D := by
    change star D = D
    simp only [D, star_sub, star_mul, star_star, hh.star_eq, mul_assoc]
  have hnorm : ‖D‖ ≤ C := norm_le_of_unit_selfAdjoint_quadratic D hD hC (by
    intro x hx
    simpa only [D, sub_apply, inner_sub_left, Complex.sub_re,
      mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left] using hquad x hx)
  have heq : h * (u : H →L[ℂ] H) - (u : H →L[ℂ] H) * h =
      -(u : H →L[ℂ] H) * D := by
    have hu := Unitary.mul_star_self_of_mem u.property
    symm
    calc
      _ = ((u : H →L[ℂ] H) * star (u : H →L[ℂ] H)) * h *
          (u : H →L[ℂ] H) - (u : H →L[ℂ] H) * h := by
        dsimp [D]
        noncomm_ring
      _ = _ := by rw [hu, one_mul]
  rw [heq, neg_mul, norm_neg, CStarRing.norm_coe_unitary_mul]
  exact hnorm

/-- The scalar lower bound `1/2` in the recovery argument converts its
`141δ` quadratic estimate into the `282δ` unitary commutator estimate. -/
theorem norm_commutator_le_two_eighty_two (h : H →L[ℂ] H) (hh : IsSelfAdjoint h)
    (u : unitary (H →L[ℂ] H)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hquad : ∀ x : H, ∃ c : ℝ, 1 / 2 ≤ c ∧
      c * |(inner ℂ (h x) x).re - (inner ℂ (h ((u : H →L[ℂ] H) x))
        ((u : H →L[ℂ] H) x)).re| ≤ 141 * δ * ‖x‖ ^ 2) :
    ‖h * (u : H →L[ℂ] H) - (u : H →L[ℂ] H) * h‖ ≤ 282 * δ := by
  apply norm_commutator_le_of_quadratic h hh u (by positivity)
  intro x
  obtain ⟨c, hc, hcx⟩ := hquad x
  nlinarith [abs_nonneg ((inner ℂ (h x) x).re -
    (inner ℂ (h ((u : H →L[ℂ] H) x)) ((u : H →L[ℂ] H) x)).re)]

end KadisonKastler

end OAI
