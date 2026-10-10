import OAI.NumberTheory.Ostmann.ZeroDensity.DensityHeadCutoff
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityTailAssembly
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDyadicPartition

namespace OAI

/-! # A uniform sixth-log bound for all growing partial smoothed squares -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators Classical

 theorem densityFiniteSquare_partial_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ N → 1 ≤ Q → ∀ T : ℝ,
      1 ≤ T → 1 ≤ Real.log N → 10 * (Q : ℝ) * T ≤ N → ∀ J : ℕ,
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ∫ t in Icc (-T) T,
        ‖∑ n ∈ Finset.Icc 1 (2 ^ J * N),
          densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n‖ ^ 2) ≤
          C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * (Real.log N) ^ 6 := by
  obtain ⟨CH, hCH, hhead⟩ := densityFiniteSquare_head_mean
  obtain ⟨CT, hCT, htail⟩ := densityFiniteSquare_tail_assembly
  refine ⟨2 * CH + 16 * CT, by positivity, ?_⟩
  intro N Q hN hQ T hT hL hscale J F hF
  let H := fun (χ : PrimitiveComplexCharacter) (t : ℝ) =>
    ∑ n ∈ Finset.Icc 1 N, densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n
  let R := fun (χ : PrimitiveComplexCharacter) (t : ℝ) =>
    ∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ioc (2 ^ j * N) (2 ^ (j + 1) * N),
      densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n
  have hH (χ : PrimitiveComplexCharacter) : ContinuousOn (H χ) (Icc (-T) T) :=
    densityFiniteSquare_continuousOn χ _ (fun n hn => (Finset.mem_Icc.mp hn).1) T hT
  have hR (χ : PrimitiveComplexCharacter) : ContinuousOn (R χ) (Icc (-T) T) := by
    apply continuousOn_finsetSum
    intro j _
    apply densityFiniteSquare_continuousOn χ _ _ T hT
    intro n hn
    have hn' := (Finset.mem_Ioc.mp hn).1
    omega
  have hpoint (χ : PrimitiveComplexCharacter) (t : ℝ) :
      ‖H χ t + R χ t‖ ^ 2 ≤ 2 * ‖H χ t‖ ^ 2 + 2 * ‖R χ t‖ ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (H χ t) (R χ t)) 2
    nlinarith [sq_nonneg (‖H χ t‖ - ‖R χ t‖)]
  have hm (χ : PrimitiveComplexCharacter) :
      (∫ t in Icc (-T) T, ‖H χ t + R χ t‖ ^ 2) ≤
        2 * (∫ t in Icc (-T) T, ‖H χ t‖ ^ 2) +
          2 * (∫ t in Icc (-T) T, ‖R χ t‖ ^ 2) := by
    have hh : Integrable (fun t => ‖H χ t‖ ^ 2) (volume.restrict (Icc (-T) T)) :=
      ((hH χ).norm.pow 2).integrableOn_Icc
    have hr : Integrable (fun t => ‖R χ t‖ ^ 2) (volume.restrict (Icc (-T) T)) :=
      ((hR χ).norm.pow 2).integrableOn_Icc
    have hi := (hh.const_mul 2).add (hr.const_mul 2)
    have hb := integral_mono (((hH χ).add (hR χ)).norm.pow 2).integrableOn_Icc hi (hpoint χ)
    simp only [Pi.add_apply, Pi.pow_apply] at hb
    have hadd := integral_add (hh.const_mul 2) (hr.const_mul 2)
    rw [hadd, integral_const_mul, integral_const_mul] at hb
    exact hb
  have hlog : (1 + Real.log N) ^ 3 ≤ 8 * (Real.log N) ^ 6 := by
    have hbase : 1 + Real.log N ≤ 2 * (Real.log N) ^ 2 := by nlinarith
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + Real.log N) hbase 3
    nlinarith
  calc
    _ = ∑ χ ∈ F, ∫ t in Icc (-T) T, ‖H χ t + R χ t‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro χ _
      apply integral_congr_ae
      filter_upwards with t
      rw [density_dyadic_partition N J hN]
    _ ≤ ∑ χ ∈ F, (2 * (∫ t in Icc (-T) T, ‖H χ t‖ ^ 2) +
        2 * (∫ t in Icc (-T) T, ‖R χ t‖ ^ 2)) := Finset.sum_le_sum (fun χ _ => hm χ)
    _ = 2 * (∑ χ ∈ F, ∫ t in Icc (-T) T, ‖H χ t‖ ^ 2) +
        2 * (∑ χ ∈ F, ∫ t in Icc (-T) T, ‖R χ t‖ ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * (CH * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * (Real.log N) ^ 6) +
        2 * (CT * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * (1 + Real.log N) ^ 3) := by
      exact add_le_add (mul_le_mul_of_nonneg_left (hhead N Q hQ T hT hL hscale F hF) (by norm_num))
        (mul_le_mul_of_nonneg_left (htail N Q hN hQ T hT hscale J F hF) (by norm_num))
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_left hlog
        (show 0 ≤ 2 * CT * ((N : ℝ) + (Q : ℝ) ^ 2 * T) by positivity)
      nlinarith

end Ostmann

end OAI
