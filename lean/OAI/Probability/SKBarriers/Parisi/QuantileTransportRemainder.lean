import Mathlib
import OAI.Probability.SKBarriers.Parisi.QuantileMinimizer
import OAI.Probability.SKBarriers.Parisi.QuantileBoundary

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem admissibleQuantiles_segment {k : ℕ} {A B : Fin (k+1) → ℝ}
    (hA : A∈admissibleQuantiles k) (hB : B∈admissibleQuantiles k)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) : (1-t) • A+t • B∈admissibleQuantiles k := by
  constructor
  · intro i j hij
    exact add_le_add (mul_le_mul_of_nonneg_left (hA.1 hij) (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left (hB.1 hij) ht.1)
  · intro j
    change (1-t)*A j+t*B j∈Icc (0:ℝ) 1
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (hA.2 j).1) (mul_nonneg ht.1 (hB.2 j).1)
    · have H₁ := mul_le_mul_of_nonneg_left (hA.2 j).2 (sub_nonneg.mpr ht.2)
      have H₂ := mul_le_mul_of_nonneg_left (hB.2 j).2 ht.1
      linarith

theorem quantileSegment_hasDerivAt {k : ℕ} (A B : Fin (k+1) → ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (1-t) • A+t • B) (B-A) t := by
  apply hasDerivAt_pi.mpr
  intro j
  have H := (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).mul_const (A j)).add
    ((hasDerivAt_id t).mul_const (B j))
  exact H.congr_deriv (by simp; ring)

theorem extendedQuantileParisi_segment_derivative {k : ℕ} (β : ℝ)
    (A B : Fin (k+1) → ℝ) (hA : ∀ j, 0≤cumulativeGapMap k A j)
    (hB : ∀ j, 0<cumulativeGapMap k B j) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun t : ℝ => extendedQuantileParisi k β ((1-t) • A+t • B))
      ((β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(B j-A j)*
        (((1-t) • A+t • B) j-quantileOverlapMean k β ((1-t) • A+t • B) j)) (Icc (0:ℝ) 1) t := by
  by_cases h : t=0
  · subst t
    simpa only [sub_zero,one_smul,zero_smul,add_zero] using
      (extendedQuantileParisi_hasDerivWithinAt_segment β A B hA hB).mono Icc_subset_Ici_self
  · have hp : 0<t := lt_of_le_of_ne ht.1 (Ne.symm h)
    apply (extendedQuantileParisi_hasDerivAt β _ (quantileSegment_hasDerivAt A B t) _).hasDerivWithinAt
    intro j
    simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) (hA j)) (mul_pos hp (hB j))

theorem quantile_transport_remainder_strict {k : ℕ} (β : ℝ)
    (A B : Fin (k+1) → ℝ) (hA : ∀ j, 0≤cumulativeGapMap k A j)
    (hB : ∀ j, 0<cumulativeGapMap k B j) {g : ℝ → ℝ} (hg : Continuous g)
    {M : ℝ} (herr : ∀ t∈Icc (0:ℝ) 1, ∀ j : Fin (k+1),
      |(((1-t) • A+t • B) j-quantileOverlapMean k β ((1-t) • A+t • B) j)-
        g (((1-t) • A+t • B) j)|≤M) :
    |extendedQuantileParisi k β B-extendedQuantileParisi k β A-
      (β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*∫ s in A j..B j, g s|≤
      (β^2/2)*(∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*|B j-A j|)*M := by
  let Q := fun t : ℝ => (1-t) • A+t • B
  let F := fun t : ℝ => extendedQuantileParisi k β (Q t)-
    (β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*∫ s in A j..Q t j, g s
  let d := fun t : ℝ => (β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(B j-A j)*
    ((Q t j-quantileOverlapMean k β (Q t) j)-g (Q t j))
  have hd (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivWithinAt F (d t) (Icc (0:ℝ) 1) t := by
    have hG (j : Fin (k+1)) : HasDerivAt (fun t => ((k+1:ℕ):ℝ)⁻¹*∫ s in A j..Q t j, g s)
        (((k+1:ℕ):ℝ)⁻¹*(g (Q t j)*(B j-A j))) t := by
      have H := (intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable (A j) (Q t j))
        (hg.stronglyMeasurableAtFilter volume (𝓝 (Q t j))) hg.continuousAt).comp t
        ((hasDerivAt_pi.mp (quantileSegment_hasDerivAt A B t)) j)
      exact H.const_mul _
    have H := (extendedQuantileParisi_segment_derivative β A B hA hB ht).sub
      ((HasDerivAt.fun_sum (u:=Finset.univ) (fun j _ => hG j)).const_mul (β^2/2)).hasDerivWithinAt
    apply H.congr_deriv
    dsimp only [d,Q]
    rw [← mul_sub,← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hb (t : ℝ) (ht : t∈Ico (0:ℝ) 1) : ‖d t‖≤
      (β^2/2)*(∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*|B j-A j|)*M := by
    rw [Real.norm_eq_abs]
    dsimp only [d]
    rw [abs_mul,abs_of_nonneg (show 0≤β^2/2 by positivity),mul_assoc,Finset.sum_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [abs_mul,abs_mul,abs_of_nonneg (show 0≤((k+1:ℕ):ℝ)⁻¹ by positivity)]
    exact mul_le_mul_of_nonneg_left (herr t ⟨ht.1,ht.2.le⟩ j) (by positivity)
  have H := norm_image_sub_le_of_norm_deriv_le_segment_01' hd hb
  simpa only [F,Q,sub_self,zero_smul,zero_add,one_smul,sub_zero,add_zero,
    intervalIntegral.integral_same,mul_zero,Finset.sum_const_zero,Real.norm_eq_abs,
    sub_right_comm] using H

end SK.Analytic

end
end

end OAI
