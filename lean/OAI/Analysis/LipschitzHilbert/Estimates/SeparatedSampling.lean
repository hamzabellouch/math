import OAI.Analysis.LipschitzHilbert.Estimates.IntervalPoincare

namespace OAI

/-! The sampling estimate needed for a band primitive: use disjoint
intervals at the band scale, independently of the larger mesh spacing. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem sample_interval_energy (A : ℝ → ℝ) (hA : Differentiable ℝ A)
    (hA2 : MemLp A 2 volume) (hd2 : MemLp (deriv A) 2 volume)
    (a : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    δ * A a ^ 2 ≤ 2 * (∫ x in Ico a (a + δ), A x ^ 2) +
      2 * δ ^ 2 * ∫ x in Ico a (a + δ), deriv A x ^ 2 := by
  have hab : a < a + δ := lt_add_of_pos_right a hδ
  let energy := ∫ x in Icc a (a + δ), deriv A x ^ 2
  have hpoint : ∀ᵐ y ∂volume.restrict (Icc a (a + δ)),
      A a ^ 2 ≤ 2 * A y ^ 2 + 2 * δ * energy := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have hp := interval_pair_energy A hab.le (fun x _ => hA x)
      (hd2.restrict _) (show a ∈ Icc a (a + δ) from ⟨le_rfl, hab.le⟩) hy
    simp only [Real.norm_eq_abs, sq_abs, add_sub_cancel_left] at hp
    nlinarith [sq_nonneg (A a - 2 * A y)]
  have h := integral_mono_ae (integrable_const (A a ^ 2))
    (((hA2.restrict (Icc a (a + δ))).integrable_sq.const_mul 2).add
      (integrable_const (2 * δ * energy))) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add ((hA2.restrict (Icc a (a + δ))).integrable_sq.const_mul 2)
      (integrable_const _), integral_const_mul, integral_const, integral_const] at h
  have hmass : (volume.restrict (Icc a (a + δ))).real univ = δ := by
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc, add_sub_cancel_left,
      ENNReal.toReal_ofReal hδ.le]
  simp only [smul_eq_mul, hmass, energy, integral_Icc_eq_integral_Ico] at h
  nlinarith only [h]

theorem separated_sample_sum (A : ℝ → ℝ) (hA : Differentiable ℝ A)
    (hA2 : MemLp A 2 volume) (hd2 : MemLp (deriv A) 2 volume)
    (N : ℕ) (sample : Fin N → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hseparated : ∀ i j, i < j → sample i + δ ≤ sample j) :
    (∑ i, A (sample i) ^ 2) ≤
      (2 / δ) * (∫ x, A x ^ 2) + 2 * δ * ∫ x, deriv A x ^ 2 := by
  let cell := fun i => Ico (sample i) (sample i + δ)
  have hdisj : Pairwise (fun i j => Disjoint (cell i) (cell j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    rcases lt_or_gt_of_ne hij with h | h
    · exact (not_lt_of_ge (hseparated i j h)) (hxj.1.trans_lt hxi.2)
    · exact (not_lt_of_ge (hseparated j i h)) (hxi.1.trans_lt hxj.2)
  have hsumA : (∑ i, ∫ x in cell i, A x ^ 2) ≤ ∫ x, A x ^ 2 := by
    rw [← integral_iUnion_fintype (fun _ => measurableSet_Ico) hdisj
      (fun _ => hA2.integrable_sq.integrableOn)]
    exact setIntegral_le_integral hA2.integrable_sq (by filter_upwards with x; exact sq_nonneg _)
  have hsumd : (∑ i, ∫ x in cell i, deriv A x ^ 2) ≤ ∫ x, deriv A x ^ 2 := by
    rw [← integral_iUnion_fintype (fun _ => measurableSet_Ico) hdisj
      (fun _ => hd2.integrable_sq.integrableOn)]
    exact setIntegral_le_integral hd2.integrable_sq (by filter_upwards with x; exact sq_nonneg _)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => sample_interval_energy A hA hA2 hd2 (sample i) hδ)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at h
  have htotal : δ * (∑ i, A (sample i) ^ 2) ≤
      2 * (∫ x, A x ^ 2) + 2 * δ ^ 2 * ∫ x, deriv A x ^ 2 := by
    dsimp only [cell] at hsumA hsumd
    nlinarith [mul_le_mul_of_nonneg_left hsumd (sq_nonneg δ)]
  calc
    _ ≤ (2 * (∫ x, A x ^ 2) + 2 * δ ^ 2 * ∫ x, deriv A x ^ 2) / δ :=
      (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using htotal)
    _ = _ := by field_simp

end LipschitzHilbert

end

end OAI
