import Mathlib
import OAI.Probability.SKBarriers.Parisi.QuantileClamp
import OAI.Probability.SKBarriers.Parisi.QuantileVariation

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem extendedQuantileParisi_lipschitz_positive {k : ℕ} (β : ℝ) (A B : Fin (k+1) → ℝ)
    (hA : ∀ j, A j ∈ Set.Icc 0 1) (hB : ∀ j, B j ∈ Set.Icc 0 1)
    (hgA : ∀ j, 0 < cumulativeGapMap k A j) (hgB : ∀ j, 0 < cumulativeGapMap k B j) :
    |extendedQuantileParisi k β B-extendedQuantileParisi k β A| ≤
      (β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*|B j-A j| := by
  let Q := fun t : ℝ => (1-t) • A+t • B
  let d := fun t => (β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(B j-A j)*
    (Q t j-quantileOverlapMean k β (Q t) j)
  have hQ (t : ℝ) : HasDerivAt Q (B-A) t := by
    apply hasDerivAt_pi.mpr
    intro j
    have H := (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).mul_const (A j)).add
      ((hasDerivAt_id t).mul_const (B j))
    exact H.congr_deriv (by simp; ring)
  have hg (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (j : Fin (k+1)) : 0 < cumulativeGapMap k (Q t) j := by
    simp only [Q,map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    by_cases h : t=0
    · simpa [h] using hgA j
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr ht.2) (hgA j).le) (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm h)) (hgB j))
  have hb (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (j : Fin (k+1)) : Q t j ∈ Set.Icc 0 1 := by
    change (1-t)*A j+t*B j ∈ Set.Icc 0 1
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (hA j).1) (mul_nonneg ht.1 (hB j).1)
    · have h1 := mul_le_mul_of_nonneg_left (hA j).2 (sub_nonneg.mpr ht.2)
      have h2 := mul_le_mul_of_nonneg_left (hB j).2 ht.1
      linarith
  have hd (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      HasDerivAt (fun t => extendedQuantileParisi k β (Q t)) (d t) t :=
    extendedQuantileParisi_hasDerivAt β Q (hQ t) (hg t ht)
  have hbound (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      ‖d t‖ ≤ (β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*|B j-A j| := by
    rw [Real.norm_eq_abs]
    dsimp only [d]
    rw [abs_mul,abs_of_nonneg (show 0 ≤ β^2/2 by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    have hr := quantileOverlapMean_bounds k β (Q t) j
    have hdif : |Q t j-quantileOverlapMean k β (Q t) j| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [(hb t ht j).1,(hb t ht j).2,hr.1,hr.2]
    rw [abs_mul,abs_mul,abs_of_nonneg (show 0 ≤ ((k+1:ℕ):ℝ)⁻¹ by positivity)]
    exact mul_le_of_le_one_right (by positivity) hdif
  have H := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (hd t ht).hasDerivWithinAt) (fun t ht => hbound t ⟨ht.1,ht.2.le⟩)
  simpa only [Q,sub_self,zero_smul,one_smul,zero_add,sub_zero,add_zero,Real.norm_eq_abs] using H

def strictQuantile (k : ℕ) (j : Fin (k+1)) : ℝ := ((j.val:ℝ)+1)/((k:ℝ)+2)

theorem strictQuantile_gap (k : ℕ) (j : Fin (k+1)) :
    cumulativeGapMap k (strictQuantile k) j = 1/((k:ℝ)+2) := by
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [cumulativeGapMap_zero,strictQuantile]
  · simp only [cumulativeGapMap_succ,strictQuantile,Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one]
    ring

theorem strictQuantile_mem (k : ℕ) (j : Fin (k+1)) : strictQuantile k j ∈ Set.Icc 0 1 := by
  have hj : (j.val:ℝ)+1 ≤ (k:ℝ)+1 := by exact_mod_cast Nat.succ_le_of_lt j.isLt
  unfold strictQuantile
  constructor
  · positivity
  · apply (div_le_one (by positivity)).mpr
    linarith

def regularizeQuantile (k : ℕ) (Q : Fin (k+1) → ℝ) (ε : ℝ) : Fin (k+1) → ℝ :=
  (1-ε) • Q+ε • strictQuantile k

theorem regularizeQuantile_positive {k : ℕ} (Q : Fin (k+1) → ℝ)
    (hQ : ∀ j, 0 ≤ cumulativeGapMap k Q j) {ε : ℝ} (hε : ε ∈ Set.Ioc 0 1) (j : Fin (k+1)) :
    0 < cumulativeGapMap k (regularizeQuantile k Q ε) j := by
  simp only [regularizeQuantile,map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,strictQuantile_gap]
  exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hε.2) (hQ j))
    (mul_pos hε.1 (by positivity))

theorem regularizeQuantile_mem {k : ℕ} (Q : Fin (k+1) → ℝ) (hQ : ∀ j, Q j ∈ Set.Icc 0 1)
    {ε : ℝ} (hε : ε ∈ Set.Icc 0 1) (j : Fin (k+1)) :
    regularizeQuantile k Q ε j ∈ Set.Icc 0 1 := by
  change (1-ε)*Q j+ε*strictQuantile k j ∈ Set.Icc 0 1
  have hR := strictQuantile_mem k j
  constructor
  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hε.2) (hQ j).1) (mul_nonneg hε.1 hR.1)
  · have H1 := mul_le_mul_of_nonneg_left (hQ j).2 (sub_nonneg.mpr hε.2)
    have H2 := mul_le_mul_of_nonneg_left hR.2 hε.1
    linarith

theorem regularizeQuantile_tendsto (k : ℕ) (Q : Fin (k+1) → ℝ) :
    Tendsto (fun n : ℕ => regularizeQuantile k Q (1/((n:ℝ)+1))) atTop (𝓝 Q) := by
  have H : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [regularizeQuantile,sub_zero,one_smul,zero_smul,add_zero] using
    (((tendsto_const_nhds (x := (1:ℝ))).sub H).smul (tendsto_const_nhds (x := Q))).add
      (H.smul (tendsto_const_nhds (x := strictQuantile k)))

theorem extendedQuantileParisi_lipschitz {k : ℕ} (β : ℝ) (A B : Fin (k+1) → ℝ)
    (hA : ∀ j, A j ∈ Set.Icc 0 1) (hB : ∀ j, B j ∈ Set.Icc 0 1)
    (hmA : Monotone A) (hmB : Monotone B) :
    |extendedQuantileParisi k β B-extendedQuantileParisi k β A| ≤
      (β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*|B j-A j| := by
  have hgA := (cumulativeGapMap_nonneg_iff k A).mpr ⟨(hA 0).1,hmA⟩
  have hgB := (cumulativeGapMap_nonneg_iff k B).mpr ⟨(hB 0).1,hmB⟩
  let ε := fun n : ℕ => 1/((n:ℝ)+1)
  have hε (n : ℕ) : ε n ∈ Set.Ioc 0 1 := by
    dsimp only [ε]
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) n]
  have H (n : ℕ) : |extendedQuantileParisi k β (regularizeQuantile k B (ε n))-
      extendedQuantileParisi k β (regularizeQuantile k A (ε n))| ≤
      (β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*|B j-A j| := by
    apply (extendedQuantileParisi_lipschitz_positive β _ _
      (regularizeQuantile_mem A hA ⟨(hε n).1.le,(hε n).2⟩)
      (regularizeQuantile_mem B hB ⟨(hε n).1.le,(hε n).2⟩)
      (regularizeQuantile_positive A hgA (hε n)) (regularizeQuantile_positive B hgB (hε n))).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have he : regularizeQuantile k B (ε n) j-regularizeQuantile k A (ε n) j = (1-ε n)*(B j-A j) := by
      simp only [regularizeQuantile,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      ring
    rw [he,abs_mul,abs_of_nonneg (sub_nonneg.mpr (hε n).2)]
    exact mul_le_of_le_one_left (abs_nonneg _) (by linarith [(hε n).1])
  have HA := (extendedQuantileParisi_continuous k β).continuousAt.tendsto.comp (regularizeQuantile_tendsto k A)
  have HB := (extendedQuantileParisi_continuous k β).continuousAt.tendsto.comp (regularizeQuantile_tendsto k B)
  exact le_of_tendsto (HB.sub HA).abs (Eventually.of_forall H)
end SK.Analytic

end
end

end

end OAI
