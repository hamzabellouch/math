import OAI.Analysis.BernoulliCone.GroundState

namespace OAI

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff
namespace Bernoulli.SobolevCalculus

lemma cutPrimitive_eq_zero_of_nonpos (n : ℕ) {t : ℝ} (ht : t ≤ 0) :
    cutPrimitive n t = 0 := by
  unfold cutPrimitive
  rw [intervalIntegral.integral_symm]
  have hz : (∫ s in t..(0:ℝ), cutSlope n s) = 0 := by
    apply intervalIntegral.integral_zero_ae
    exact ae_of_all _ fun s hs => by
      have hs0 : s ≤ 0 := (mem_Ioc.mp (uIoc_of_le ht ▸ hs)).2
      have hh : ((n:ℝ)+1)*s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hs0
      simp [cutSlope,max_eq_right hh]
  simp [hz]

def innerCut (n : ℕ) (t : ℝ) : ℝ := cutPrimitive n (t - 1/((n:ℝ)+1))
def innerSlope (n : ℕ) (t : ℝ) : ℝ := cutSlope n (t - 1/((n:ℝ)+1))

lemma innerCut_zero (n : ℕ) : innerCut n 0 = 0 := by
  apply cutPrimitive_eq_zero_of_nonpos
  simp only [zero_sub]
  exact neg_nonpos.mpr (by positivity)
lemma innerCut_deriv (n : ℕ) (t : ℝ) : HasDerivAt (innerCut n) (innerSlope n t) t := by
  convert! (cutPrimitive_deriv n (t-1/((n:ℝ)+1))).comp t ((hasDerivAt_id t).sub_const (1/((n:ℝ)+1))) using 1
  dsimp [innerSlope]
  ring
lemma innerCut_contDiff (n : ℕ) : ContDiff ℝ 1 (innerCut n) :=
  (cutPrimitive_contDiff n).comp (contDiff_id.sub contDiff_const)
lemma innerCut_lipschitz (n : ℕ) : LipschitzWith 1 (innerCut n) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [innerCut,Real.dist_eq,sub_sub_sub_cancel_right,NNReal.coe_one,one_mul] using (cutPrimitive_lipschitz n).dist_le_mul (x-1/((n:ℝ)+1)) (y-1/((n:ℝ)+1))
lemma innerSlope_continuous (n : ℕ) : Continuous (innerSlope n) :=
  (cutSlope_continuous n).comp (continuous_id.sub continuous_const)
lemma innerSlope_norm_le (n : ℕ) (t : ℝ) : ‖innerSlope n t‖ ≤ 1 := cutSlope_norm_le _ _
lemma innerCut_vanish (n : ℕ) {t : ℝ} (ht : t ≤ 1/((n:ℝ)+1)) : innerCut n t = 0 :=
  cutPrimitive_eq_zero_of_nonpos n (sub_nonpos.mpr ht)

lemma innerCut_tendsto (t : ℝ) : Tendsto (fun n => innerCut n t) atTop (𝓝 (max t 0)) := by
  have he : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 (0:ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hd : Tendsto (fun n => innerCut n t - cutPrimitive n t) atTop (𝓝 (0:ℝ)) := by
    apply squeeze_zero_norm _ he
    intro n
    have hh := (cutPrimitive_lipschitz n).norm_sub_le (t-1/((n:ℝ)+1)) t
    simpa only [innerCut,NNReal.coe_one,one_mul,sub_sub_cancel_left,norm_neg,Real.norm_of_nonneg (by positivity : 0≤1/((n:ℝ)+1))] using hh
  simpa only [sub_add_cancel,zero_add] using hd.add (cutPrimitive_tendsto t)

lemma innerSlope_tendsto (t : ℝ) :
    Tendsto (fun n => innerSlope n t) atTop (𝓝 (if 0<t then (1:ℝ) else 0)) := by
  by_cases ht : 0<t
  · simp only [ite_eq_left ht]
    have hg : Tendsto (fun n : ℕ => ((n:ℝ)+1)*t-1) atTop atTop :=
      Filter.tendsto_atTop_add_const_right _ (-1) ((tendsto_atTop_mono (fun n : ℕ => (show (n:ℝ)≤(n:ℝ)+1 by linarith))
        tendsto_natCast_atTop_atTop).atTop_mul_const ht)
    apply tendsto_const_nhds.congr'
    filter_upwards [hg.eventually_ge_atTop 1] with n hn
    have he : ((n:ℝ)+1)*(t-1/((n:ℝ)+1))=((n:ℝ)+1)*t-1 := by
      field_simp
    dsimp only [innerSlope,cutSlope]
    rw [he,max_eq_left (by linarith),min_eq_right hn]
  · simp only [ite_eq_right ht]
    have hz (n : ℕ) : innerSlope n t=0 := by
      have hm : ((n:ℝ)+1)*(t-1/((n:ℝ)+1))≤0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith [show 0≤1/((n:ℝ)+1) by positivity])
      dsimp only [innerSlope,cutSlope]
      rw [max_eq_right hm]
      norm_num
    simp only [hz]
    exact tendsto_const_nhds

lemma h10_innerCut {d : ℕ} {D : Set (Space d)} {w : Space d → ℝ} {G : Space d → Space d}
    (hD : IsOpen D) (hw : H10 D w G) (n : ℕ) :
    H10 D (innerCut n ∘ w) (fun x => innerSlope n (w x) • G x) := by
  have hh := h10_comp_C1 hD hw (innerCut_contDiff n) (innerCut_lipschitz n) (innerCut_zero n)
  have he : deriv (innerCut n)=innerSlope n := funext fun t => (innerCut_deriv n t).deriv
  rwa [he] at hh

theorem h10_positive_domain {d : ℕ} {D : Set (Space d)}
    {w U : Space d → ℝ} {G : Space d → Space d}
    (hD : IsOpen D) (hDc : IsCompact (closure D)) (hw : H10 D w G)
    (hU : Continuous U) (hwn : ∀x, 0≤w x) (hbound : ∀x, w x≤U x)
    (hw0 : ∀x, x∉D → w x=0) :
    H10 {x | 0<U x} w (D.indicator G) := by
  let P := {x | 0<U x}
  have hP : IsOpen P := isOpen_lt continuous_const hU
  have hwg : H10 univ w (D.indicator G) := by
    have hh := hw.zero_extension hD.measurableSet (subset_univ D)
    have he : D.indicator w=w := by
      ext x
      by_cases hx:x∈D <;> simp [hx,hw0 x]
    rwa [he] at hh
  have hwp := hwg.1.mono (subset_univ P)
  have hcut (n : ℕ) : H10 P (innerCut n ∘ w) (fun x=>innerSlope n (w x) • D.indicator G x) := by
    have hh := (h10_innerCut isOpen_univ hwg n).1.mono (subset_univ P)
    have hs : tsupport (innerCut n ∘ w) ⊆ closure D ∩ {x | 1/((n:ℝ)+1)≤U x} := by
      apply closure_minimal _ (isClosed_closure.inter (isClosed_le continuous_const hU))
      intro x hx
      have hx' : innerCut n (w x)≠0 := hx
      have hlt : 1/((n:ℝ)+1)<w x := lt_of_not_ge (fun hn=>hx' (innerCut_vanish n hn))
      refine ⟨subset_closure ?_,(hlt.le.trans (hbound x))⟩
      by_contra hn
      rw [hw0 x hn] at hlt
      have : 0<1/((n:ℝ)+1) := by positivity
      linarith
    apply h10_of_local_compact_support hP hh
    · exact (hDc.inter_right (isClosed_le continuous_const hU)).of_isClosed_subset (isClosed_tsupport _) hs
    · intro x hx
      exact lt_of_lt_of_le (by positivity : 0<1/((n:ℝ)+1)) (hs hx).2
  apply h10_of_strong hwp.1 hwp.2.1 hcut
  · apply tendsto_eLpNorm_zero_of_dominated
      (fun n=>((innerCut_lipschitz n).continuous.comp_aestronglyMeasurable hwp.1.aestronglyMeasurable).sub hwp.1.aestronglyMeasurable)
      (hwp.1.norm.const_smul (2:ℝ))
    · intro n
      exact ae_of_all _ fun x=>by
        have hn : ‖innerCut n (w x)‖≤‖w x‖ := by
          simpa [innerCut_zero] using (innerCut_lipschitz n).norm_sub_le (w x) 0
        calc ‖innerCut n (w x)-w x‖ ≤ ‖innerCut n (w x)‖+‖w x‖ := norm_sub_le _ _
             _ ≤ ‖((2:ℝ) • fun y=>‖w y‖) x‖ := by
                simp only [Pi.smul_apply,smul_eq_mul,norm_mul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2),norm_norm]
                linarith
    · exact ae_of_all _ fun x=>by
        simpa only [Pi.sub_apply,Function.comp_apply,max_eq_left (hwn x),sub_self] using (innerCut_tendsto (w x)).sub_const (w x)
  · have hz := gradient_zero_on_zero_set isOpen_univ hwg.1
    simp only [Measure.restrict_univ] at hz
    apply tendsto_eLpNorm_zero_of_dominated
      (fun n=>(((innerSlope_continuous n).comp_aestronglyMeasurable hwp.1.aestronglyMeasurable).smul hwp.2.1.aestronglyMeasurable).sub hwp.2.1.aestronglyMeasurable)
      (hwp.2.1.norm.const_smul (2:ℝ))
    · intro n
      exact ae_of_all _ fun x=>by
        calc ‖innerSlope n (w x) • D.indicator G x-D.indicator G x‖ ≤
            ‖innerSlope n (w x) • D.indicator G x‖+‖D.indicator G x‖ := norm_sub_le _ _
          _ ≤ ‖((2:ℝ) • fun y=>‖D.indicator G y‖) x‖ := by
            rw [norm_smul]
            have hh:=mul_le_mul_of_nonneg_right (innerSlope_norm_le n (w x)) (norm_nonneg (D.indicator G x))
            simp only [Pi.smul_apply,smul_eq_mul,norm_mul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2),norm_norm]
            linarith
    · filter_upwards [ae_restrict_of_ae hz] with x hx
      by_cases hp : 0<w x
      · have ht := (innerSlope_tendsto (w x)).smul (tendsto_const_nhds : Tendsto (fun _ : ℕ=>D.indicator G x) atTop (𝓝 (D.indicator G x)))
        simpa only [Pi.sub_apply,Pi.smul_apply',ite_eq_left hp,one_smul,sub_self] using ht.sub_const (D.indicator G x)
      · have hwz : w x=0 := le_antisymm (not_lt.mp hp) (hwn x)
        simp only [Pi.sub_apply,Pi.smul_apply',hx hwz,smul_zero,sub_self]
        exact tendsto_const_nhds

theorem h10_positive_domain_inter {d : ℕ} {D : Set (Space d)}
    {S : Set (Space d)} (hS : IsOpen S) (hDS : closure D ⊆ S)
    {w U : Space d → ℝ} {G : Space d → Space d}
    (hD : IsOpen D) (hDc : IsCompact (closure D)) (hw : H10 D w G)
    (hU : Continuous U) (hwn : ∀x, 0≤w x) (hbound : ∀x, w x≤U x)
    (hw0 : ∀x, x∉D → w x=0) :
    H10 ({x | 0<U x} ∩ S) w (D.indicator G) := by
  let P := {x | 0<U x} ∩ S
  have hP : IsOpen P := (isOpen_lt continuous_const hU).inter hS
  have hwg : H10 univ w (D.indicator G) := by
    have hh := hw.zero_extension hD.measurableSet (subset_univ D)
    have he : D.indicator w=w := by
      ext x
      by_cases hx:x∈D <;> simp [hx,hw0 x]
    rwa [he] at hh
  have hwp := hwg.1.mono (subset_univ P)
  have hcut (n : ℕ) : H10 P (innerCut n ∘ w) (fun x=>innerSlope n (w x) • D.indicator G x) := by
    have hh := (h10_innerCut isOpen_univ hwg n).1.mono (subset_univ P)
    have hs : tsupport (innerCut n ∘ w) ⊆ closure D ∩ {x | 1/((n:ℝ)+1)≤U x} := by
      apply closure_minimal _ (isClosed_closure.inter (isClosed_le continuous_const hU))
      intro x hx
      have hx' : innerCut n (w x)≠0 := hx
      have hlt : 1/((n:ℝ)+1)<w x := lt_of_not_ge (fun hn=>hx' (innerCut_vanish n hn))
      refine ⟨subset_closure ?_,(hlt.le.trans (hbound x))⟩
      by_contra hn
      rw [hw0 x hn] at hlt
      have : 0<1/((n:ℝ)+1) := by positivity
      linarith
    apply h10_of_local_compact_support hP hh
    · exact (hDc.inter_right (isClosed_le continuous_const hU)).of_isClosed_subset (isClosed_tsupport _) hs
    · intro x hx
      exact ⟨lt_of_lt_of_le (by positivity : 0<1/((n:ℝ)+1)) (hs hx).2, hDS (hs hx).1⟩
  apply h10_of_strong hwp.1 hwp.2.1 hcut
  · apply tendsto_eLpNorm_zero_of_dominated
      (fun n=>((innerCut_lipschitz n).continuous.comp_aestronglyMeasurable hwp.1.aestronglyMeasurable).sub hwp.1.aestronglyMeasurable)
      (hwp.1.norm.const_smul (2:ℝ))
    · intro n
      exact ae_of_all _ fun x=>by
        have hn : ‖innerCut n (w x)‖≤‖w x‖ := by
          simpa [innerCut_zero] using (innerCut_lipschitz n).norm_sub_le (w x) 0
        calc ‖innerCut n (w x)-w x‖ ≤ ‖innerCut n (w x)‖+‖w x‖ := norm_sub_le _ _
             _ ≤ ‖((2:ℝ) • fun y=>‖w y‖) x‖ := by
                simp only [Pi.smul_apply,smul_eq_mul,norm_mul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2),norm_norm]
                linarith
    · exact ae_of_all _ fun x=>by
        simpa only [Pi.sub_apply,Function.comp_apply,max_eq_left (hwn x),sub_self] using (innerCut_tendsto (w x)).sub_const (w x)
  · have hz := gradient_zero_on_zero_set isOpen_univ hwg.1
    simp only [Measure.restrict_univ] at hz
    apply tendsto_eLpNorm_zero_of_dominated
      (fun n=>(((innerSlope_continuous n).comp_aestronglyMeasurable hwp.1.aestronglyMeasurable).smul hwp.2.1.aestronglyMeasurable).sub hwp.2.1.aestronglyMeasurable)
      (hwp.2.1.norm.const_smul (2:ℝ))
    · intro n
      exact ae_of_all _ fun x=>by
        calc ‖innerSlope n (w x) • D.indicator G x-D.indicator G x‖ ≤
            ‖innerSlope n (w x) • D.indicator G x‖+‖D.indicator G x‖ := norm_sub_le _ _
          _ ≤ ‖((2:ℝ) • fun y=>‖D.indicator G y‖) x‖ := by
            rw [norm_smul]
            have hh:=mul_le_mul_of_nonneg_right (innerSlope_norm_le n (w x)) (norm_nonneg (D.indicator G x))
            simp only [Pi.smul_apply,smul_eq_mul,norm_mul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2),norm_norm]
            linarith
    · filter_upwards [ae_restrict_of_ae hz] with x hx
      by_cases hp : 0<w x
      · have ht := (innerSlope_tendsto (w x)).smul (tendsto_const_nhds : Tendsto (fun _ : ℕ=>D.indicator G x) atTop (𝓝 (D.indicator G x)))
        simpa only [Pi.sub_apply,Pi.smul_apply',ite_eq_left hp,one_smul,sub_self] using ht.sub_const (D.indicator G x)
      · have hwz : w x=0 := le_antisymm (not_lt.mp hp) (hwn x)
        simp only [Pi.sub_apply,Pi.smul_apply',hx hwz,smul_zero,sub_self]
        exact tendsto_const_nhds

end Bernoulli.SobolevCalculus

end
end

end OAI
