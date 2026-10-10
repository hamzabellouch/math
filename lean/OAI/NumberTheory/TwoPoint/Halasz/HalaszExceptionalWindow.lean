import OAI.NumberTheory.TwoPoint.Halasz.HalaszWindowIntegral

namespace OAI

/-! A localized exceptional interval in the Halasz Perron integral.
This retains decay in the distance from the minimizing frequency instead
of requiring a uniform bound throughout a large central window. -/
namespace TwoPointCorrelations

open MeasureTheory

lemma halasz_exceptional_cauchy_weight (c t : ℝ)
    (ht : t ∈ Set.Ioc (c-1/2) (c+1/2)) :
    1/Real.sqrt (1+t^2) ≤ 3/(1+|c|) := by
  have hs : 0 < Real.sqrt (1+t^2) := Real.sqrt_pos.mpr (by positivity)
  have hs1 : 1 ≤ Real.sqrt (1+t^2) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith
  have hst : |t| ≤ Real.sqrt (1+t^2) := by
    apply (Real.le_sqrt (abs_nonneg _) (by positivity)).mpr
    rw [sq_abs]
    linarith
  have hdiff : |c-t| ≤ 1/2 := abs_le.mpr ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have hc : |c| ≤ 1/2+|t| := by
    have hh := abs_add_le (c-t) t
    rw [sub_add_cancel] at hh
    linarith
  apply (div_le_div_iff₀ hs (by positivity : 0 < 1+|c|)).mpr
  nlinarith

theorem halasz_window_middle_exception {x δ T A W c : ℝ}
    (hx : 0 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hT : 0 ≤ T)
    (hA : 0 ≤ A) (hW : 0 ≤ W)
    (P Q F : ℝ → ℂ) (hP : Continuous P) (hQ : Continuous Q)
    (hi : IntegrableOn (fun t => P t*Q t*F t*
      halaszPerronWindowKernel x δ (1+(t:ℂ)*Complex.I)) (Set.Ioc (-T) T))
    (hF : ∀ t ∈ Set.Ioc (-T) T, t ∉ Set.Ioc (c-1/2) (c+1/2) → ‖F t‖ ≤ A)
    (hFW : ∀ t ∈ Set.Ioc (-T) T, ‖F t‖ ≤ W) :
    ‖∫ t in -T..T, P t*Q t*F t*
      halaszPerronWindowKernel x δ (1+(t:ℂ)*Complex.I)‖ ≤
      (4*x*A)*(Real.sqrt (∫ t in -T..T, ‖P t‖^2)*
        Real.sqrt (∫ t in -T..T, ‖Q t‖^2*(1+t^2)⁻¹)) +
      (12*x*W/(1+|c|))*(Real.sqrt (∫ t in (c-1/2)..(c+1/2), ‖P t‖^2)*
        Real.sqrt (∫ t in (c-1/2)..(c+1/2), ‖Q t‖^2)) := by
  let D := Set.Ioc (-T) T
  let E := Set.Ioc (c-1/2) (c+1/2)
  let I := fun t => P t*Q t*F t*halaszPerronWindowKernel x δ (1+(t:ℂ)*Complex.I)
  let G := fun t => ‖P t‖*‖Q t‖/Real.sqrt (1+t^2)
  let J := fun t => ‖P t‖*‖Q t‖
  have hG : Continuous G := (hP.norm.mul hQ.norm).div
    ((continuous_const.add (continuous_id.pow 2)).sqrt)
    (fun t => ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  have hJ : Continuous J := hP.norm.mul hQ.norm
  have hGD : IntegrableOn G D :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : -T ≤ T)).mp
      (hG.intervalIntegrable _ _)
  have hJE : IntegrableOn J E :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : c-1/2 ≤ c+1/2)).mp
      (hJ.intervalIntegrable _ _)
  have hsmall : ‖∫ t in D \ E, I t‖ ≤ (4*x*A)*∫ t in D, G t := by
    calc
      _ ≤ ∫ t in D \ E, (4*x*A)*G t := by
        apply norm_integral_le_of_norm_le ((hGD.mono_set Set.sdiff_subset).const_mul _)
        apply (ae_restrict_mem (measurableSet_Ioc.diff measurableSet_Ioc)).mono
        intro t ht
        have hk := halasz_perron_window_bound hx hδ hδ1 t
        rw [halasz_vertical_norm] at hk
        dsimp [I,G]
        simp only [norm_mul]
        calc
          _ ≤ (‖P t‖*‖Q t‖*A)*(4*x/Real.sqrt (1+t^2)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hF t ht.1 ht.2) (by positivity))
              hk (norm_nonneg _) (by positivity)
          _ = _ := by ring
      _ ≤ ∫ t in D, (4*x*A)*G t := setIntegral_mono_set
        (hGD.const_mul _) (Filter.Eventually.of_forall (fun t => by dsimp [G]; positivity))
        (Filter.Eventually.of_forall Set.sdiff_subset)
      _ = _ := integral_const_mul _ _
  have hlarge : ‖∫ t in D ∩ E, I t‖ ≤ (12*x*W/(1+|c|))*∫ t in E, J t := by
    calc
      _ ≤ ∫ t in D ∩ E, (12*x*W/(1+|c|))*J t := by
        apply norm_integral_le_of_norm_le ((hJE.mono_set Set.inter_subset_right).const_mul _)
        apply (ae_restrict_mem (measurableSet_Ioc.inter measurableSet_Ioc)).mono
        intro t ht
        have hk := halasz_perron_window_bound hx hδ hδ1 t
        rw [halasz_vertical_norm] at hk
        have hw := halasz_exceptional_cauchy_weight c t ht.2
        have hkernel : ‖halaszPerronWindowKernel x δ (1+(t:ℂ)*Complex.I)‖ ≤
            12*x/(1+|c|) := by
          apply hk.trans
          have hh := mul_le_mul_of_nonneg_left hw (show 0 ≤ 4*x by positivity)
          convert hh using 1 <;> ring
        dsimp [I,J]
        simp only [norm_mul]
        calc
          _ ≤ (‖P t‖*‖Q t‖*W)*(12*x/(1+|c|)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hFW t ht.1) (by positivity))
              hkernel (norm_nonneg _) (by positivity)
          _ = _ := by ring
      _ ≤ ∫ t in E, (12*x*W/(1+|c|))*J t := setIntegral_mono_set
        (hJE.const_mul _) (Filter.Eventually.of_forall (fun t => by dsimp [J]; positivity))
        (Filter.Eventually.of_forall Set.inter_subset_right)
      _ = _ := integral_const_mul _ _
  have hsplit := integral_inter_add_sdiff (f := I) (s := D) (t := E) measurableSet_Ioc hi
  have hnorm := norm_add_le (∫ t in D ∩ E, I t) (∫ t in D \ E, I t)
  rw [hsplit] at hnorm
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  apply (hnorm.trans (add_le_add hlarge hsmall)).trans
  have hcs := halasz_weighted_integral_cauchy_schwarz (by linarith : -T ≤ T) P Q hP hQ
  have hce := halasz_integral_cauchy_schwarz (by linarith : c-1/2 ≤ c+1/2)
    (fun t => ‖P t‖) (fun t => ‖Q t‖) hP.norm hQ.norm
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)] at hcs
  rw [intervalIntegral.integral_of_le (by linarith : c-1/2 ≤ c+1/2)] at hce
  change (∫ t in D, G t) ≤ _ at hcs
  change (∫ t in E, J t) ≤ _ at hce
  nlinarith [mul_le_mul_of_nonneg_left hcs (show 0 ≤ 4*x*A by positivity),
    mul_le_mul_of_nonneg_left hce (show 0 ≤ 12*x*W/(1+|c|) by positivity)]

end TwoPointCorrelations

end OAI
