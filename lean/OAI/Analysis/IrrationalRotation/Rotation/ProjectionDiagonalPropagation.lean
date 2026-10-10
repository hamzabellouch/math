import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive

namespace OAI

namespace InvariantProjection

open scoped InnerProductSpace
open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem projection_inner_eq_inner_projected {P : H →L[ℂ] H}
    (hP : IsStarProjection P) (e : H) :
    ⟪e, P e⟫_ℂ = ⟪P e, P e⟫_ℂ := by
  have hid : P (P e) = P e := by
    exact congrArg (fun A : H →L[ℂ] H => A e) hP.isIdempotentElem
  have hs := hP.isSelfAdjoint.isSymmetric e (P e)
  simpa only [ContinuousLinearMap.coe_coe, hid] using hs.symm

theorem projection_inner_eq_zero_iff {P : H →L[ℂ] H}
    (hP : IsStarProjection P) (e : H) :
    ⟪e, P e⟫_ℂ = 0 ↔ P e = 0 := by
  rw [projection_inner_eq_inner_projected hP, inner_self_eq_zero]

theorem projection_inner_eq_self_iff {P : H →L[ℂ] H}
    (hP : IsStarProjection P) (e : H) :
    ⟪e, P e⟫_ℂ = ⟪e, e⟫_ℂ ↔ P e = e := by
  have h := projection_inner_eq_zero_iff hP.one_sub e
  simp only [sub_apply, one_apply_eq_self, inner_sub_right, sub_eq_zero] at h
  exact (eq_comm.trans h).trans eq_comm

omit [CompleteSpace H] in

theorem projection_invariance_apply {P Q D : H →L[ℂ] H}
    (hinv : (1 - Q) * D * P = 0) (v : H) :
    Q (D (P v)) = D (P v) := by
  have h := congrArg (fun A : H →L[ℂ] H => A v) hinv
  simp only [mul_apply_eq_comp, sub_apply,
    one_apply_eq_self, zero_apply, sub_eq_zero] at h
  exact h.symm

theorem projection_kernel_propagation {P Q D : H →L[ℂ] H}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    {e : H} {a : ℂ} (ha : a ≠ 0)
    (hcoord : ∀ v : H, ⟪e, D v⟫_ℂ = a * ⟪e, v⟫_ℂ)
    (hinv : (1 - Q) * D * P = 0) (hQe : Q e = 0) :
    P e = 0 := by
  apply (projection_inner_eq_zero_iff hP e).mp
  have hfixed := projection_invariance_apply hinv e
  have hz : ⟪e, D (P e)⟫_ℂ = 0 := by
    calc
      ⟪e, D (P e)⟫_ℂ = ⟪e, Q (D (P e))⟫_ℂ := by rw [hfixed]
      _ = ⟪Q e, D (P e)⟫_ℂ := (hQ.isSelfAdjoint.isSymmetric e (D (P e))).symm
      _ = 0 := by rw [hQe, inner_zero_left]
  rw [hcoord] at hz
  exact (mul_eq_zero.mp hz).resolve_left ha

omit [CompleteSpace H] in

theorem projection_fixed_propagation {P Q D : H →L[ℂ] H}
    {e : H} {a : ℂ} (ha : a ≠ 0) (heigen : D e = a • e)
    (hinv : (1 - Q) * D * P = 0) (hPe : P e = e) :
    Q e = e := by
  have hfixed := projection_invariance_apply hinv e
  rw [hPe, heigen, map_smul] at hfixed
  exact (smul_right_injective H ha) hfixed

theorem projection_diagonal_propagation {P Q D : H →L[ℂ] H}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    {e : H} {a : ℂ} (ha : a ≠ 0)
    (hcoord : ∀ v : H, ⟪e, D v⟫_ℂ = a * ⟪e, v⟫_ℂ)
    (heigen : D e = a • e) (hinv : (1 - Q) * D * P = 0) :
    (⟪e, Q e⟫_ℂ = 0 → ⟪e, P e⟫_ℂ = 0) ∧
    (⟪e, P e⟫_ℂ = ⟪e, e⟫_ℂ → ⟪e, Q e⟫_ℂ = ⟪e, e⟫_ℂ) := by
  constructor
  · intro h
    exact (projection_inner_eq_zero_iff hP e).mpr
      (projection_kernel_propagation hP hQ ha hcoord hinv
        ((projection_inner_eq_zero_iff hQ e).mp h))
  · intro h
    exact (projection_inner_eq_self_iff hQ e).mpr
      (projection_fixed_propagation ha heigen hinv
        ((projection_inner_eq_self_iff hP e).mp h))

omit [CompleteSpace H] in
private theorem complex_inner_self_re_eq_norm_sq (v : H) :
    (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) v

theorem projection_re_inner_eq_zero_iff {P : H →L[ℂ] H}
    (hP : IsStarProjection P) (e : H) :
    (⟪e, P e⟫_ℂ).re = 0 ↔ P e = 0 := by
  rw [projection_inner_eq_inner_projected hP, complex_inner_self_re_eq_norm_sq,
    sq_eq_zero_iff, norm_eq_zero]

theorem projection_re_inner_eq_self_iff {P : H →L[ℂ] H}
    (hP : IsStarProjection P) (e : H) :
    (⟪e, P e⟫_ℂ).re = ‖e‖ ^ 2 ↔ P e = e := by
  have h := projection_re_inner_eq_zero_iff hP.one_sub e
  simp only [sub_apply, one_apply_eq_self, inner_sub_right,
    Complex.sub_re, complex_inner_self_re_eq_norm_sq, sub_eq_zero] at h
  exact (eq_comm.trans h).trans eq_comm

theorem projection_re_inner_bounds {P : H →L[ℂ] H}
    (hP : IsStarProjection P) (e : H) :
    0 ≤ (⟪e, P e⟫_ℂ).re ∧ (⟪e, P e⟫_ℂ).re ≤ ‖e‖ ^ 2 := by
  have hn : ∀ {Q : H →L[ℂ] H}, IsStarProjection Q → 0 ≤ (⟪e, Q e⟫_ℂ).re := by
    intro Q hQ
    rw [projection_inner_eq_inner_projected hQ]
    exact inner_self_nonneg (𝕜 := ℂ)
  refine ⟨hn hP, ?_⟩
  have hc := hn hP.one_sub
  simp only [sub_apply, one_apply_eq_self, inner_sub_right,
    Complex.sub_re, complex_inner_self_re_eq_norm_sq] at hc
  exact sub_nonneg.mp hc

theorem selfAdjoint_coordinate_law {D : H →L[ℂ] H}
    (hD : IsSelfAdjoint D) {e : H} {a : ℝ}
    (heigen : D e = (a : ℂ) • e) (v : H) :
    ⟪e, D v⟫_ℂ = (a : ℂ) * ⟪e, v⟫_ℂ := by
  calc
    ⟪e, D v⟫_ℂ = ⟪D e, v⟫_ℂ := (hD.isSymmetric e v).symm
    _ = (a : ℂ) * ⟪e, v⟫_ℂ := by
      rw [heigen, inner_smul_left]
      simp

theorem projection_real_diagonal_propagation {P Q D : H →L[ℂ] H}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hD : IsSelfAdjoint D) {e : H} (he : ‖e‖ = 1)
    {a : ℝ} (ha : a ≠ 0) (heigen : D e = (a : ℂ) • e)
    (hinv : (1 - Q) * D * P = 0) :
    ((⟪e, Q e⟫_ℂ).re = 0 → (⟪e, P e⟫_ℂ).re = 0) ∧
    ((⟪e, P e⟫_ℂ).re = 1 → (⟪e, Q e⟫_ℂ).re = 1) := by
  have hac : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  constructor
  · intro h
    exact (projection_re_inner_eq_zero_iff hP e).mpr
      (projection_kernel_propagation hP hQ hac
        (selfAdjoint_coordinate_law hD heigen) hinv
        ((projection_re_inner_eq_zero_iff hQ e).mp h))
  · intro h
    have hPe : P e = e := (projection_re_inner_eq_self_iff hP e).mp (by simpa [he] using h)
    have hQe := projection_fixed_propagation hac heigen hinv hPe
    simpa [he] using (projection_re_inner_eq_self_iff hQ e).mpr hQe

end InvariantProjection

end OAI
