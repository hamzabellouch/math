import Mathlib
import OAI.Probability.SKGap.Localization.PartitionLogLipschitz

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped BigOperators NNReal Topology

lemma exists_gaussian_tail_quantile {p : ℝ} (hp : 0 < p) :
    ∃ c : ℝ, 0 < c ∧ exp (-2*c^2/π^2) < p := by
  let c : ℝ := sqrt (π^2/2*(|log p|+1))
  have hc : 0 < c := sqrt_pos.mpr (mul_pos (div_pos (sq_pos_of_pos pi_pos) (by norm_num)) (by positivity))
  have hc2 : c^2=π^2/2*(|log p|+1) := sq_sqrt (by positivity)
  refine ⟨c,hc,?_⟩
  have he : -2*c^2/π^2= -(|log p|+1) := by rw [hc2];field_simp
  rw [he]
  apply lt_of_lt_of_eq ?_ (exp_log hp)
  apply exp_lt_exp.mpr
  linarith only [neg_abs_le (log p)]

lemma eventually_sqrt_cost_le_linear {δ c : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) :
    ∀ᶠ n : ℕ in atTop, log 2+c*sqrt (n:ℝ) ≤ δ*(n:ℝ)/2 := by
  have hl : 0 ≤ log (2:ℝ) := log_nonneg (by norm_num)
  have hlarge : ∀ᶠ n : ℕ in atTop, (4*c/δ)^2+4*log 2/δ ≤ (n:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hlarge] with n hn
  have hn0 : (0:ℝ) ≤ n := by positivity
  have hs : 4*c/δ ≤ sqrt (n:ℝ) := by
    apply (sq_le_sq₀ (by positivity) (sqrt_nonneg _)).mp
    rw [sq_sqrt hn0]
    linarith only [hn,div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hl) hδ.le]
  have hs' := (div_le_iff₀ hδ).mp hs
  have he := sq_sqrt hn0
  have hm := mul_le_mul_of_nonneg_right hs' (sqrt_nonneg (n:ℝ))
  have hn' : 4*log 2/δ ≤ (n:ℝ) := by linarith only [hn,sq_nonneg (4*c/δ)]
  have hl' := (div_le_iff₀ hδ).mp hn'
  have hm' : 4*c*sqrt (n:ℝ) ≤ δ*(n:ℝ) := hm.trans_eq (by
    calc sqrt (n:ℝ)*δ*sqrt (n:ℝ) = δ*(sqrt (n:ℝ))^2 := by ring
         _ = δ*(n:ℝ) := by rw [he])
  linarith only [hm',hl']

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped BigOperators NNReal Topology

lemma gaussianSpinPartition_log_mean_lower {j c : ℝ} (hj0 : 0 ≤ j) (hj : j < 1)
    (hc : 0 < c) (hpc : exp (-2*c^2/π^2) < 1/(4*quadraticGaussianBound j))
    {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r) (hnr : (n:ℝ)*r ≤ j) :
    log (∫ g,gaussianSpinPartition n r g ∂gaussianCoordinates (Edge n))-log 2-c*sqrt (n:ℝ) ≤
      ∫ g,log (gaussianSpinPartition n r g) ∂gaussianCoordinates (Edge n) := by
  have hM := gaussianSpinPartition_mean_pos (n:=n) hr
  have hsub : {g | (∫ g,gaussianSpinPartition n r g ∂gaussianCoordinates (Edge n))/2 ≤ gaussianSpinPartition n r g} ⊆
      {g | log (∫ g,gaussianSpinPartition n r g ∂gaussianCoordinates (Edge n))-log 2 ≤ log (gaussianSpinPartition n r g)} := by
    intro g hg
    simp only [mem_ofPred_eq] at hg ⊢
    have h := log_le_log (div_pos hM (by norm_num)) hg
    rwa [log_div hM.ne' (by norm_num : (2:ℝ) ≠ 0)] at h
  exact gaussian_log_anchor (f:=fun g=>log (gaussianSpinPartition n r g)) (gaussianSpinPartition_log_lipschitz hr (hnr.trans hj.le))
    (by exact_mod_cast sqrt_pos.mpr (show (0:ℝ) < n by exact_mod_cast hn)) hc hpc
    ((gaussianSpinPartition_positive_probability hj0 hj hr hnr).trans
      (measureReal_mono hsub (measure_ne_top _ _)))

lemma gaussianSpinPartition_lower_tail_bound {j c δ : ℝ} (hj0 : 0 ≤ j) (hj : j < 1)
    (hc : 0 < c) (hpc : exp (-2*c^2/π^2) < 1/(4*quadraticGaussianBound j)) (hδ : 0 < δ)
    {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r) (hnr : (n:ℝ)*r ≤ j)
    (hbudget : log 2+c*sqrt (n:ℝ) ≤ δ*(n:ℝ)/2) :
    (gaussianCoordinates (Edge n)).real
      {g | gaussianSpinPartition n r g/(∫ g,gaussianSpinPartition n r g ∂gaussianCoordinates (Edge n)) < exp (-δ*(n:ℝ))} ≤
      exp (-δ^2*(n:ℝ)/(2*π^2)) := by
  have hnp : (0:ℝ) < n := by exact_mod_cast hn
  have hM := gaussianSpinPartition_mean_pos (n:=n) hr
  have ha := gaussianSpinPartition_log_mean_lower hj0 hj hc hpc hn hr hnr
  have hsub : {g | gaussianSpinPartition n r g/(∫ g,gaussianSpinPartition n r g ∂gaussianCoordinates (Edge n)) < exp (-δ*(n:ℝ))} ⊆
      {g | log (gaussianSpinPartition n r g)-(∫ g,log (gaussianSpinPartition n r g) ∂gaussianCoordinates (Edge n)) ≤ -(δ*(n:ℝ)/2)} := by
    intro g hg
    simp only [mem_ofPred_eq] at hg
    have hg' := (div_lt_iff₀ hM).mp hg
    have hlog := log_lt_log (gaussianSpinPartition_pos n r g) hg'
    rw [log_mul (exp_pos _).ne' hM.ne',log_exp] at hlog
    simp only [mem_ofPred_eq]
    linarith only [hlog,ha,hbudget]
  have htail := gaussianProduct_lower_tail_lipschitz (f:=fun g=>log (gaussianSpinPartition n r g))
    (gaussianSpinPartition_log_lipschitz hr (hnr.trans hj.le))
    (show (0:ℝ≥0) < ⟨sqrt (n:ℝ),sqrt_nonneg _⟩ from sqrt_pos.mpr hnp)
    (show 0 ≤ δ*(n:ℝ)/2 by positivity)
  have he : -2*(δ*(n:ℝ)/2)^2/(π^2*(sqrt (n:ℝ))^2)= -δ^2*(n:ℝ)/(2*π^2) := by
    rw [sq_sqrt hnp.le]
    field_simp
  change _ ≤ exp (-2*(δ*(n:ℝ)/2)^2/(π^2*(sqrt (n:ℝ))^2)) at htail
  rw [he] at htail
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans htail

lemma gaussianSpinPartition_lower_tail_tendsto {j : ℝ} (hj0 : 0 ≤ j) (hj : j < 1)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ=>(gaussianCoordinates (Edge n)).real
      {g | gaussianSpinPartition n (j/(n:ℝ)) g/
        (∫ g,gaussianSpinPartition n (j/(n:ℝ)) g ∂gaussianCoordinates (Edge n)) < exp (-δ*(n:ℝ))}) atTop (𝓝 0) := by
  obtain ⟨c,hc,hpc⟩ := exists_gaussian_tail_quantile
    (show 0 < 1/(4*quadraticGaussianBound j) by
      have hB := quadraticGaussianBound_ge_one hj0 hj; positivity)
  have hb : ∀ᶠ n : ℕ in atTop,
      (gaussianCoordinates (Edge n)).real {g | gaussianSpinPartition n (j/(n:ℝ)) g/
        (∫ g,gaussianSpinPartition n (j/(n:ℝ)) g ∂gaussianCoordinates (Edge n)) < exp (-δ*(n:ℝ))} ≤
      exp (-δ^2*(n:ℝ)/(2*π^2)) := by
    filter_upwards [eventually_gt_atTop 0,eventually_sqrt_cost_le_linear hδ hc.le] with n hn hbudget
    have hnp : (0:ℝ) < n := by exact_mod_cast hn
    apply gaussianSpinPartition_lower_tail_bound hj0 hj hc hpc hδ hn (div_nonneg hj0 hnp.le) _ hbudget
    rw [mul_div_cancel₀ _ hnp.ne']
  have ht : Tendsto (fun n : ℕ=>exp (-δ^2*(n:ℝ)/(2*π^2))) atTop (𝓝 0) := by
    have hpos : 0 < δ^2/(2*π^2) := by positivity
    have hh : Tendsto (fun n : ℕ=>(δ^2/(2*π^2))*(n:ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hpos
    convert tendsto_exp_neg_atTop_nhds_zero.comp hh using 1; ext n; congr 1; ring
  exact squeeze_zero' (Eventually.of_forall (fun _=>measureReal_nonneg)) hb ht
end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped BigOperators NNReal Topology

lemma gaussian_disorder_hasLaw (β : ℝ) (n : ℕ) :
    HasLaw (fun g : Disorder n=>fun e=>sqrt (β^2/(n:ℝ))*g e) (disorderLaw β n)
      (gaussianCoordinates (Edge n)) := by
  have hr : 0 ≤ β^2/(n:ℝ) := by positivity
  have hl (e : Edge n) : HasLaw (fun g : Disorder n=>sqrt (β^2/(n:ℝ))*g e)
      (gaussianReal 0 (Real.toNNReal (β^2/(n:ℝ)))) (gaussianCoordinates (Edge n)) := by
    have h := gaussianReal_const_mul (coordinate_hasLaw (κ:=Edge n) e) (sqrt (β^2/(n:ℝ)))
    have hv : (⟨(sqrt (β^2/(n:ℝ)))^2,sq_nonneg _⟩:ℝ≥0)*1=Real.toNNReal (β^2/(n:ℝ)) := by
      apply NNReal.eq
      change (sqrt (β^2/(n:ℝ)))^2*1=↑(Real.toNNReal (β^2/(n:ℝ)))
      rw [mul_one,sq_sqrt hr,Real.coe_toNNReal _ hr]
    rw [mul_zero] at h
    convert h using 1
    exact congrArg (gaussianReal 0) hv.symm
  exact iIndepFun.hasLaw_pi hl ((iIndepFun_pi (fun _ : Edge n=>aemeasurable_id)).comp
    (fun _=>fun x : ℝ=>sqrt (β^2/(n:ℝ))*x) (fun _=>by fun_prop))

lemma partition_zero_measurable (n : ℕ) : Measurable (fun g : Disorder n=>partition g 0) := by
  have he : (fun g : Disorder n=>partition g 0)=gaussianSpinPartition n 1 := by
    ext g
    rw [gaussianSpinPartition_eq_partition]
    simp only [sqrt_one,one_mul]
  rw [he]
  exact gaussianSpinPartition_measurable n 1

lemma disorder_partition_mean (β : ℝ) (n : ℕ) :
    (∫ g,partition g 0 ∂disorderLaw β n)=
      ∫ g,gaussianSpinPartition n (β^2/(n:ℝ)) g ∂gaussianCoordinates (Edge n) := by
  have h := (gaussian_disorder_hasLaw β n).integral_comp (partition_zero_measurable n).aestronglyMeasurable
  simpa only [Function.comp_def,gaussianSpinPartition_eq_partition] using h.symm

theorem disorder_partition_lower_tail {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ=>(disorderLaw β n).real
      {g | partition g 0/(∫ g,partition g 0 ∂disorderLaw β n) < exp (-δ*(n:ℝ))}) atTop (𝓝 0) := by
  have ht := gaussianSpinPartition_lower_tail_tendsto (sq_nonneg β) (show β^2 < 1 by nlinarith) hδ
  apply ht.congr
  intro n
  rw [← (gaussian_disorder_hasLaw β n).measureReal_eq
    (measurableSet_lt ((partition_zero_measurable n).div_const _) measurable_const)]
  simp only [disorder_partition_mean,gaussianSpinPartition_eq_partition]
end SKGap
end
end

end OAI
