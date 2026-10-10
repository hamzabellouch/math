import Mathlib
import OAI.Probability.SKRatio.Matrices.AugmentedSquares

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open SKRatioClock.Regression MatrixNet Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma shiftedDisorder_hasLaw (β : ℝ) :
    HasLaw (fun g : Disorder n => fun e => g e+β^2/(n:ℝ)) (law β n) (disorderLaw β n) := by
  have hi : iIndepFun (fun e (g : Disorder n) => g e) (disorderLaw β n) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hl (e : Edge n) : HasLaw (fun g : Disorder n => g e)
      (gaussianReal 0 (Real.toNNReal (β^2/(n:ℝ)))) (disorderLaw β n) :=
    (measurePreserving_eval (fun _ : Edge n => gaussianReal 0 (Real.toNNReal (β^2/(n:ℝ)))) e).hasLaw
  apply iIndepFun.hasLaw_pi _ (hi.comp (fun _ x => x+β^2/(n:ℝ)) (fun _ => by fun_prop))
  intro e
  simpa only [zero_add,Function.comp_def] using gaussianReal_add_const (hl e) (β^2/(n:ℝ))

lemma coupling_shift (β : ℝ) (g : Disorder n) :
    Matrix.of (coupling (fun e => g e+β^2/(n:ℝ))) =
      Matrix.of (coupling g)+Matrix.of (coupling (fun _ => β^2/(n:ℝ))) := by
  ext i j
  simp only [Matrix.of_apply,Matrix.add_apply,coupling]
  split_ifs <;> ring

lemma meanMatrix_opNorm_bound (β : ℝ) :
    euclideanOpNorm (coupling (fun _ : Edge n => β^2/(n:ℝ))) ≤ β^2 := by
  have hentry (i j : Fin n) : |coupling (fun _ : Edge n => β^2/(n:ℝ)) i j| ≤ β^2/(n:ℝ) := by
    unfold coupling
    split_ifs <;> simp [abs_of_nonneg (div_nonneg (sq_nonneg β) (Nat.cast_nonneg n)),
      div_nonneg (sq_nonneg β) (Nat.cast_nonneg n)]
  have hr (i : Fin n) : ∑ j, |coupling (fun _ : Edge n => β^2/(n:ℝ)) i j| ≤ β^2 := by
    have hn : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (Nat.zero_lt_of_lt i.isLt))
    calc
      _ ≤ ∑ _j : Fin n, β^2/(n:ℝ) := Finset.sum_le_sum (fun j _ => hentry i j)
      _ = β^2 := by simp [mul_div_cancel₀ _ hn]
  exact matrix_opNorm_le_schur _ _ (sq_nonneg β) hr (fun j => by
    simpa only [coupling_symm] using hr j)

lemma shifted_opNorm_bound (β : ℝ) (g : Disorder n) :
    euclideanOpNorm (coupling (fun e => g e+β^2/(n:ℝ))) ≤
      euclideanOpNorm (coupling g)+β^2 := by
  change ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (Matrix.of (coupling (fun e => g e+β^2/(n:ℝ))))‖ ≤ _
  rw [coupling_shift,map_add]
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  exact meanMatrix_opNorm_bound β

lemma original_norm_rare {β δ : ℝ} (hβ : 0<β) (hδ : 0<δ) :
    ExponentiallyRare (disorderLaw β) (fun n => {g : Disorder n | 2*β+δ<euclideanOpNorm (coupling g)}) := by
  have hc : 0<(δ/2)^2/(Real.pi^2*β^2) := by positivity
  have hd : 0<(δ/2)^2/(8*β^2) := by positivity
  apply exponentiallyRare_of_polynomial _ _ (C := 4) (c := min ((δ/2)^2/(Real.pi^2*β^2)) ((δ/2)^2/(8*β^2)))
    (by norm_num) (lt_min hc hd) 1
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : 0<n := lt_of_lt_of_le (by norm_num) hn
  have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn
  have ht := Gaussian.coupling_norm_tail hβ hδ.le hn0
  rw [←ENNReal.ofReal_toReal (measure_ne_top (disorderLaw β n) _)]
  apply ENNReal.ofReal_le_ofReal
  refine ht.trans ?_
  have ht₁ := exp_le_exp.mpr (show -((δ/2)^2/(Real.pi^2*β^2))*(n:ℝ) ≤
    -min ((δ/2)^2/(Real.pi^2*β^2)) ((δ/2)^2/(8*β^2))*(n:ℝ) by
      nlinarith [min_le_left ((δ/2)^2/(Real.pi^2*β^2)) ((δ/2)^2/(8*β^2))])
  have ht₂ := exp_le_exp.mpr (show -((δ/2)^2/(8*β^2))*(n:ℝ) ≤
    -min ((δ/2)^2/(Real.pi^2*β^2)) ((δ/2)^2/(8*β^2))*(n:ℝ) by
      nlinarith [min_le_right ((δ/2)^2/(Real.pi^2*β^2)) ((δ/2)^2/(8*β^2))])
  simp only [pow_one]
  have hm := mul_nonneg (show 0≤(n:ℝ)-1 by linarith)
    (exp_nonneg (-min ((δ/2)^2/(Real.pi^2*β^2)) ((δ/2)^2/(8*β^2))*(n:ℝ)))
  nlinarith [mul_le_mul_of_nonneg_left ht₂ (show 0≤2*(n:ℝ) by positivity)]

lemma planted_norm_rare {β δ : ℝ} (hβ : 0<β) (hδ : 0<δ) :
    ExponentiallyRare (law β) (fun n => {g : Disorder n | 2*β+β^2+δ<euclideanOpNorm (coupling g)}) := by
  obtain ⟨C,c,hC,hc,ht⟩ := original_norm_rare hβ hδ
  refine ⟨C,c,hC,hc,?_⟩
  filter_upwards [ht] with n hn
  rw [←(shiftedDisorder_hasLaw (n := n) β).measure_eq
    (isOpen_lt continuous_const Gaussian.continuous_operator_norm).measurableSet]
  refine (measure_mono ?_).trans hn
  intro g hg
  change 2*β+β^2+δ < _ at hg
  change 2*β+δ < _
  linarith [shifted_opNorm_bound β g]

lemma continuous_augmentedDisorder (β : ℝ) : Continuous (augmentedDisorder (n := n) β) := by
  unfold augmentedDisorder augmented goe
  fun_prop

lemma augmented_norm_rare {β δ : ℝ} (hβ : 0<β) (hδ : 0<δ) :
    ExponentiallyRare (fun n => standardArrayLaw (Fin n × Fin n))
      (fun n => {g | 2*β+β^2+δ<euclideanOpNorm (coupling (augmentedDisorder (n := n) β g))}) := by
  obtain ⟨C,c,hC,hc,ht⟩ := planted_norm_rare hβ hδ
  refine ⟨C,c,hC,hc,?_⟩
  filter_upwards [ht,eventually_gt_atTop 0] with n hn hn0
  rw [(augmentedDisorder_hasLaw hn0 β).measure_eq
    (isOpen_lt continuous_const Gaussian.continuous_operator_norm).measurableSet]
  exact hn

lemma centered_augmentedDiagonal_hasLaw (hn : 0<n) (β : ℝ) (i : Fin n) :
    HasLaw (fun g : (Fin n × Fin n) → ℝ => β*goe g i i)
      (gaussianReal 0 (Real.toNNReal (2*β^2/(n:ℝ)))) (standardArrayLaw (Fin n × Fin n)) := by
  have hg : HasGaussianLaw (fun g : (Fin n × Fin n) → ℝ => β*goe g i i)
      (standardArrayLaw (Fin n × Fin n)) := by
    simpa only [ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,
      smul_eq_mul,mul_comm] using (((goe_gaussian n).eval i |>.eval i).map_fun
        ((ContinuousLinearMap.id ℝ ℝ).smulRight β))
  refine ⟨hg.aemeasurable,?_⟩
  rw [hg.map_eq_gaussianReal,integral_const_mul,goe_entry_mean,mul_zero,
    ←covariance_self hg.aemeasurable,covariance_const_mul_left,covariance_const_mul_right,
    goe_entry_covariance hn]
  congr 2
  simp only [and_self,ite_true]
  ring

lemma augmented_diagonal_rare (β : ℝ) {u : ℝ} (hu : 0<u) :
    ExponentiallyRare (fun n => standardArrayLaw (Fin n × Fin n))
      (fun n => {g | ∃ i : Fin n, u< |augmentedDiagonal β g i|}) := by
  by_cases hb : β=0
  · apply (exponentiallyRare_empty (fun n => standardArrayLaw (Fin n × Fin n))).mono
    refine Eventually.of_forall ?_
    intro n g hg
    obtain ⟨i,hi⟩ := hg
    simp [augmentedDiagonal,augmented,hb,hu.not_gt] at hi
  have hb2 : 0<β^2 := sq_pos_of_ne_zero hb
  have hc : 0<u^2/(16*β^2) := by positivity
  have ht := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (β^2)
  have hbound : ∀ᶠ n in atTop, ∀ i : Fin n,
      standardArrayLaw (Fin n × Fin n) {g | u< |augmentedDiagonal β g i|} ≤
        ENNReal.ofReal (2*exp (-(u^2/(16*β^2))*n)) := by
    filter_upwards [eventually_gt_atTop 0,ht.eventually (gt_mem_nhds (by positivity : (0:ℝ)<u/2))]
      with n hn hm i
    have hnr : (0:ℝ)<n := Nat.cast_pos.mpr hn
    have hs := subgaussian_abs_tail (gaussian_hasSubgaussianMGF (centered_augmentedDiagonal_hasLaw hn β i))
      (u/2) (by positivity)
    have hv : (Real.toNNReal (2*β^2/(n:ℝ)) : ℝ)=2*β^2/(n:ℝ) := Real.coe_toNNReal _ (by positivity)
    have he : -(u/2)^2/(2*(2*β^2/(n:ℝ)))=-(u^2/(16*β^2))*(n:ℝ) := by field_simp; ring
    rw [hv,he,←ENNReal.ofReal_ofNat 2,←ENNReal.ofReal_mul (by norm_num)] at hs
    refine (measure_mono ?_).trans hs
    intro g hg
    change u/2 ≤ |β*goe g i i|
    have ha := abs_add_le (β*goe g i i) (β^2/(n:ℝ))
    rw [abs_of_nonneg (by positivity : 0≤β^2/(n:ℝ))] at ha
    change u< |β*goe g i i+β^2/(n:ℝ)| at hg
    linarith
  have hh := exponentiallyRare_iUnion_polynomial (fun n => standardArrayLaw (Fin n × Fin n))
    (fun n i => {g | u< |augmentedDiagonal β g i|}) hc (by norm_num : (0:ℝ)<2)
    (D := 1) (by norm_num) 1 (Eventually.of_forall (fun n => by simp)) hbound
  apply hh.mono
  exact Eventually.of_forall (fun n g hg => mem_iUnion.mpr hg)

end SKRatio.Planted

end

end OAI
