import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

namespace OAI

open Filter Topology

namespace Balanced.ProfileIdentifiability

noncomputable def laplaceSeries {ι : Type*} (a w : ι → ℝ) (s : ℝ) : ℝ :=
  ∑' i, a i * Real.exp (-w i * s)

theorem tendsto_rescaled_laplaceSeries {ι : Type*} (a w : ι → ℝ)
    (ha : Summable (fun i => |a i|)) (hw : Function.Injective w) (m : ι)
    (hmin : ∀ i, a i ≠ 0 → w m ≤ w i) :
    Tendsto (fun s : ℝ => Real.exp (w m * s) * laplaceSeries a w s)
      atTop (𝓝 (a m)) := by
  classical
  have hterm (i : ι) :
      Tendsto (fun s : ℝ => a i * Real.exp (-(w i - w m) * s))
        atTop (𝓝 (if i = m then a i else 0)) := by
    by_cases hi : i = m
    · subst i
      simp
    · by_cases hai : a i = 0
      · simp [hai, hi]
      · have hgt : w m < w i := lt_of_le_of_ne (hmin i hai) (fun h => hi (hw h.symm))
        have he := Real.tendsto_exp_atBot.comp
          (Filter.Tendsto.const_mul_atTop_of_neg (show -(w i - w m) < 0 by linarith)
            (tendsto_id : Tendsto (fun s : ℝ => s) atTop atTop))
        simpa [hi] using he.const_mul (a i)
  have hbound : ∀ᶠ s : ℝ in atTop, ∀ i,
      ‖a i * Real.exp (-(w i - w m) * s)‖ ≤ |a i| := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs i
    by_cases hai : a i = 0
    · simp [hai]
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (abs_nonneg _)
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [hmin i hai]) hs))
  have hsum := tendsto_tsum_of_dominated_convergence ha hterm hbound
  simp only [tsum_ite_eq] at hsum
  convert hsum using 1
  funext s
  rw [laplaceSeries, ← tsum_mul_left]
  apply tsum_congr
  intro i
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring

theorem exists_least_nonzero_exponent {ι : Type*} (a w : ι → ℝ)
    (hfinite : ∀ t : ℝ, {i | w i ≤ t}.Finite)
    (hne : ∃ i, a i ≠ 0) :
    ∃ m, a m ≠ 0 ∧ ∀ i, a i ≠ 0 → w m ≤ w i := by
  obtain ⟨j, hj⟩ := hne
  let S : Set ι := {i | w i ≤ w j ∧ a i ≠ 0}
  have hS : S.Finite := (hfinite (w j)).subset (fun _ hi => hi.1)
  obtain ⟨m, hm, hmin⟩ := Set.exists_min_image S w hS ⟨j, le_rfl, hj⟩
  refine ⟨m, hm.2, fun i hi => ?_⟩
  by_cases hle : w i ≤ w j
  · exact hmin i ⟨hle, hi⟩
  · exact hm.1.trans (le_of_not_ge hle)

theorem laplaceSeries_eq_zero_imp {ι : Type*} (a w : ι → ℝ)
    (ha : Summable (fun i => |a i|)) (hw : Function.Injective w)
    (hfinite : ∀ t : ℝ, {i | w i ≤ t}.Finite)
    (hzero : ∀ s : ℝ, 0 < s → laplaceSeries a w s = 0) :
    ∀ i, a i = 0 := by
  by_contra h
  push Not at h
  obtain ⟨m, hm, hmin⟩ := exists_least_nonzero_exponent a w hfinite h
  have hlim := tendsto_rescaled_laplaceSeries a w ha hw m hmin
  have hz : Tendsto (fun s : ℝ => Real.exp (w m * s) * laplaceSeries a w s)
      atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    simp [hzero s hs]
  exact hm (tendsto_nhds_unique hlim hz)

theorem exists_laplaceSeries_ne_zero {ι : Type*} (a w : ι → ℝ)
    (ha : Summable (fun i => |a i|)) (hw : Function.Injective w)
    (hfinite : ∀ t : ℝ, {i | w i ≤ t}.Finite)
    (hne : ∃ i, a i ≠ 0) :
    ∃ s : ℝ, 0 < s ∧ laplaceSeries a w s ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨i, hi⟩ := hne
  exact hi (laplaceSeries_eq_zero_imp a w ha hw hfinite h i)

theorem summable_laplaceTerms {ι : Type*} (a w : ι → ℝ)
    (ha : Summable (fun i => |a i|)) (hw : ∀ i, 0 ≤ w i)
    {s : ℝ} (hs : 0 ≤ s) : Summable (fun i => a i * Real.exp (-w i * s)) := by
  apply ha.of_norm_bounded
  intro i
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (abs_nonneg _)
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hw i)) hs))

theorem laplaceSeries_injective {ι : Type*} (a b w : ι → ℝ)
    (ha : Summable (fun i => |a i|)) (hb : Summable (fun i => |b i|))
    (hw0 : ∀ i, 0 ≤ w i) (hw : Function.Injective w)
    (hfinite : ∀ t : ℝ, {i | w i ≤ t}.Finite)
    (heq : ∀ s : ℝ, 0 < s → laplaceSeries a w s = laplaceSeries b w s) : a = b := by
  have hab : Summable (fun i => |a i - b i|) :=
    (ha.add hb).of_norm_bounded (fun i => by
      simpa only [Real.norm_eq_abs, abs_abs] using abs_sub (a i) (b i))
  have hz (s : ℝ) (hs : 0 < s) : laplaceSeries (a - b) w s = 0 := by
    have ha' := summable_laplaceTerms a w ha hw0 hs.le
    have hb' := summable_laplaceTerms b w hb hw0 hs.le
    simp only [laplaceSeries, Pi.sub_apply, sub_mul]
    rw [ha'.tsum_sub hb']
    exact sub_eq_zero.mpr (heq s hs)
  have h := laplaceSeries_eq_zero_imp (a - b) w hab hw hfinite hz
  funext i
  exact sub_eq_zero.mp (h i)

end Balanced.ProfileIdentifiability

end OAI
