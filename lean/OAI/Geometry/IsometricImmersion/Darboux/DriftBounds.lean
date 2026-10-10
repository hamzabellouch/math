import OAI.Geometry.IsometricImmersion.Calculus.QuotientCalculus
import Mathlib.Analysis.Normed.Group.Bounded

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Geometry

theorem explicitDriftError_scalar_bound
    (h E hy T J c BE Bh BT BJ : ℝ)
    (hc : 0 < c) (hh : c ≤ |h|)
    (hE : |E| ≤ BE) (hhy : |hy| ≤ Bh)
    (hT : |T| ≤ BT) (hJ : |J| ≤ BJ) :
    |E / h ^ 2 * (T - hy / h) + J / h| ≤
      BE / c ^ 2 * (BT + Bh / c) + BJ / c := by
  have hBE : 0 ≤ BE := (abs_nonneg E).trans hE
  have hBh : 0 ≤ Bh := (abs_nonneg hy).trans hhy
  have hBJ : 0 ≤ BJ := (abs_nonneg J).trans hJ
  have hEh : |E / h ^ 2| ≤ BE / c ^ 2 := by
    rw [abs_div, abs_pow]
    exact div_le_div₀ hBE hE (sq_pos_of_pos hc) (pow_le_pow_left₀ hc.le hh 2)
  have hhyh : |hy / h| ≤ Bh / c := by
    rw [abs_div]
    exact div_le_div₀ hBh hhy hc hh
  have hJh : |J / h| ≤ BJ / c := by
    rw [abs_div]
    exact div_le_div₀ hBJ hJ hc hh
  have htri : |T - hy / h| ≤ |T| + |hy / h| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le T (-(hy / h))
  have hsub : |T - hy / h| ≤ BT + Bh / c :=
    htri.trans (add_le_add hT hhyh)
  calc
    |E / h ^ 2 * (T - hy / h) + J / h|
        ≤ |E / h ^ 2 * (T - hy / h)| + |J / h| := abs_add_le _ _
    _ = |E / h ^ 2| * |T - hy / h| + |J / h| := by rw [abs_mul]
    _ ≤ BE / c ^ 2 * (BT + Bh / c) + BJ / c :=
      add_le_add
        (mul_le_mul hEh hsub (abs_nonneg _) (div_nonneg hBE (sq_nonneg c))) hJh

theorem explicitDriftError_pointwise_bound
    (h E T J : Coord → ℝ) (p : Coord) (c BE Bh BT BJ : ℝ)
    (hc : 0 < c) (hh : c ≤ |h p|)
    (hE : |E p| ≤ BE) (hhy : |coordPartial 1 h p| ≤ Bh)
    (hT : |T p| ≤ BT) (hJ : |J p| ≤ BJ) :
    |explicitDriftError h E T J p| ≤
      BE / c ^ 2 * (BT + Bh / c) + BJ / c := by
  exact explicitDriftError_scalar_bound (h p) (E p) (coordPartial 1 h p)
    (T p) (J p) c BE Bh BT BJ hc hh hE hhy hT hJ

theorem explicitDriftError_bounded_on_compact
    {h E T J : Coord → ℝ} {U Q : Set Coord}
    (hU : IsOpen U) (hQ : IsCompact Q) (hQU : Q ⊆ U)
    (hh : ContDiffOn ℝ ∞ h U) (hE : ContDiffOn ℝ ∞ E U)
    (hT : ContDiffOn ℝ ∞ T U) (hJ : ContDiffOn ℝ ∞ J U)
    (hne : ∀ p ∈ U, h p ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Q, |explicitDriftError h E T J p| ≤ C := by
  have hcont : ContinuousOn (explicitDriftError h E T J) Q :=
    (explicitDriftError_contDiffOn hU hh hE hT hJ hne).continuousOn.mono hQU
  obtain ⟨C, hC⟩ := hQ.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro p hp
  have hpC : |explicitDriftError h E T J p| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC p hp
  exact hpC.trans (le_max_left _ _)

end SmoothLocal.Geometry

end

end OAI
