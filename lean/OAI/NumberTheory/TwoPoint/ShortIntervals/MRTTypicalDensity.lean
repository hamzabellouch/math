import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandParameters
import Mathlib.Data.Fintype.Sets

namespace OAI

/-! The dense typical set in MRT Lemma 2.2, with a uniform translated
finite-interval formulation.  No fundamental-lemma-of-sieve input remains:
the finite Bonferroni estimate and the proved Mertens bound suffice here. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma mrt_band_count_le_scale (Q L : ℝ) (J : ℕ) (hL : 1 ≤ L)
    (hlogQ : 1 ≤ Real.log Q)
    (hmax : ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (L ^ (99 / 100 : ℝ))) :
    (J : ℝ) ≤ L := by
  by_cases hJ : J = 0
  · simp [hJ, le_trans zero_le_one hL]
  have hJ1 : 1 ≤ J := by omega
  calc
    (J : ℝ) ≤ Real.log (mrtBandUpper Q J) :=
      mrt_band_index_le_log_upper Q J hJ1 hlogQ
    _ ≤ Real.log (Real.exp (L ^ (99 / 100 : ℝ))) :=
      Real.log_le_log (Real.exp_pos _)
        (hmax J (mem_Icc.mpr ⟨hJ1, le_rfl⟩))
    _ = L ^ (99 / 100 : ℝ) := Real.log_exp _
    _ ≤ L := Real.rpow_le_self_of_one_le hL (by norm_num)

lemma mrt_band_small_error (P Q L : ℝ) (J : ℕ) (hL : 1 ≤ L)
    (hP : 2 ≤ P) (hQ : 1 < Q) (hlogQ : Real.log Q ≤ L) (hJ : (J : ℝ) ≤ L) :
    2 * J * L ^ (-100 : ℝ) ≤ 4 * Real.log P / Real.log Q := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hlP : (1 / 2 : ℝ) ≤ Real.log P := by
    have hh := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    have hmono := Real.log_le_log (show (0 : ℝ) < 2 by norm_num) hP
    norm_num at hh
    linarith
  have hp : L ^ (-100 : ℝ) ≤ (L ^ 2)⁻¹ := by
    calc
      _ ≤ L ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
      _ = _ := by rw [Real.rpow_neg hLp.le, Real.rpow_two]
  calc
    _ ≤ 2 * L * (L ^ 2)⁻¹ := by gcongr
    _ = 2 / L := by field_simp
    _ ≤ _ := by
      apply (div_le_div_iff₀ hLp (Real.log_pos hQ)).mpr
      nlinarith

/-- Every family of the explicit MRT bands below the allowed upper
cutoff has missing density `O(log P / log Q)`, uniformly in translation.
The family need not be chosen maximal. -/
theorem mrt_typical_density : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ L : ℝ in atTop, ∀ (P Q : ℝ) (J : ℕ),
      2 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
      (∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (L ^ (99 / 100 : ℝ))) →
      ∀ (A N : ℕ) [NeZero N],
      (1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ)) ≤ N →
      (uniformFiniteLaw (Fin N)).probability
        (fun n => ¬mrtTypical univ
          (fun j : {j : ℕ // j ∈ (Icc 1 J : Finset ℕ)} =>
            mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) (A + n.val)) ≤
        C * Real.log P / Real.log Q := by
  obtain ⟨C, hC, hfamily⟩ := mrt_eventually_atypical_family
  refine ⟨2 * C + 4, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 1, hfamily] with L hL hfamily
  intro P Q J hP hPQ hlogQ hmax A N _ hN
  have hQ : 1 < Q := lt_of_lt_of_le (by norm_num) (hP.trans hPQ)
  let ι := {j : ℕ // j ∈ (Icc 1 J : Finset ℕ)}
  have hh := hfamily ι (fun j => mrtBandLower P Q j) (fun j => mrtBandUpper Q j)
    (fun j => (mrt_band_endpoints P Q j (mem_Icc.mp j.property).1 hP hPQ hlogQ).1)
    (fun j => (mrt_band_endpoints P Q j (mem_Icc.mp j.property).1 hP hPQ hlogQ).2)
    (fun j => hmax j j.property) A N hN
  have hcard : Fintype.card ι = J := by simp [ι]
  have hsum : (∑ j : ι, Real.log (mrtBandLower P Q j) /
      Real.log (mrtBandUpper Q j)) =
      ∑ j ∈ Icc 1 J, Real.log (mrtBandLower P Q j) /
        Real.log (mrtBandUpper Q j) := by
    exact (sum_subtype (p := fun j : ℕ => j ∈ Icc 1 J) (Icc 1 J)
      (fun _ => Iff.rfl) (fun j => Real.log (mrtBandLower P Q j) /
        Real.log (mrtBandUpper Q j))).symm
  rw [hcard, hsum] at hh
  have hmain := mrt_band_ratio_sum P Q J (by linarith) hQ
  have hcount := mrt_band_count_le_scale Q L J hL hlogQ hmax
  by_cases hJ : J = 0
  · have hnonneg : 0 ≤ (2 * C + 4) * Real.log P / Real.log Q := by
      exact div_nonneg (mul_nonneg (by positivity)
        (Real.log_nonneg (by linarith))) (Real.log_pos hQ).le
    exact hh.trans (by simpa [hJ] using hnonneg)
  have hQmax : Q ≤ Real.exp (L ^ (99 / 100 : ℝ)) := by
    have hx := hmax 1 (mem_Icc.mpr ⟨le_rfl, by omega⟩)
    rwa [mrtBandUpper_one Q (by linarith)] at hx
  have hlogmax : Real.log Q ≤ L := by
    calc
      _ ≤ Real.log (Real.exp (L ^ (99 / 100 : ℝ))) :=
        Real.log_le_log (by linarith) hQmax
      _ = L ^ (99 / 100 : ℝ) := Real.log_exp _
      _ ≤ L := Real.rpow_le_self_of_one_le hL (by norm_num)
  have herr := mrt_band_small_error P Q L J hL hP hQ hlogmax hcount
  have hscaled := mul_le_mul_of_nonneg_left hmain hC.le
  convert hh.trans (add_le_add hscaled herr) using 1
  ring

end TwoPointCorrelations

end OAI
