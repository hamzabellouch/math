import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

variable {Omega : Type*} [MeasurableSpace Omega]
  {B : ℝ≥0 → Omega → ℝ} {mu : Measure Omega}

def brownianBridge (B : ℝ≥0 → Omega → ℝ) (T : ℝ≥0)
    (s : ℝ≥0) (w : Omega) : ℝ :=
  B s w - ((s : ℝ) / (T : ℝ)) * B T w

lemma preBrownian_bridge_indep_terminal (hB : IsPreBrownianReal B mu)
    {T : ℝ≥0} (hT : T ≠ 0) :
    IndepFun (fun w (s : Set.Iic T) => brownianBridge B T s w) (B T) mu := by
  classical
  have hind : IndepFun
      (fun w (s : Set.Iic T) => brownianBridge B T s w)
      (fun w (_ : Unit) => B T w) mu := by
    apply IsGaussianProcess.indepFun_of_covariance_eq_zero
    · apply hB.isGaussianProcess.of_isGaussianProcess
      rintro (⟨s, hs⟩ | u)
      · exact ⟨{s, T},
          { toFun x := x ⟨s, by simp⟩ - ((s : ℝ) / (T : ℝ)) * x ⟨T, by simp⟩
            map_add' x y := by simp; ring
            map_smul' c x := by simp; ring }, by simp [brownianBridge]⟩
      · exact ⟨{T},
          { toFun x := x ⟨T, by simp⟩
            map_add' x y := by simp
            map_smul' c x := by simp }, by simp⟩
    · intro s
      exact (hB.aemeasurable s).sub ((hB.aemeasurable T).const_mul _)
    · intro u
      exact hB.aemeasurable T
    · intro s u
      have : IsProbabilityMeasure mu := hB.isGaussianProcess.isProbabilityMeasure
      change cov[fun w => B s w - ((s : ℝ) / (T : ℝ)) * B T w, B T; mu] = 0
      rw [covariance_fun_sub_left, covariance_const_mul_left,
        hB.covariance_eval, hB.covariance_eval, min_eq_left s.property, min_self]
      · have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT
        simp [div_mul_cancel₀ _ hT']
      · exact (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
      · exact (hB.isGaussianProcess.hasGaussianLaw_eval T).memLp_two.const_mul _
      · exact (hB.isGaussianProcess.hasGaussianLaw_eval T).memLp_two
  simpa only [Function.comp_def, id_eq] using
    hind.comp measurable_id (measurable_pi_apply ())

omit [MeasurableSpace Omega]

lemma brownianBridge_add_drift (B : ℝ≥0 → Omega → ℝ) (sigma : Omega → ℝ)
    {T : ℝ≥0} (hT : T ≠ 0) (s : ℝ≥0) (w : Omega) :
    brownianBridge (fun t w => (t : ℝ) * sigma w + B t w) T s w =
      brownianBridge B T s w := by
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT
  simp only [brownianBridge]
  field_simp
  ring

lemma comap_past_eq_endpoint_bridge (B : ℝ≥0 → Omega → ℝ) (T : ℝ≥0) :
    MeasurableSpace.comap (fun w (s : Set.Iic T) => B s w) inferInstance =
      MeasurableSpace.comap
        (fun w => (B T w, fun s : Set.Iic T => brownianBridge B T s w)) inferInstance := by
  apply le_antisymm
  · let : MeasurableSpace Omega := MeasurableSpace.comap
      (fun w => (B T w, fun s : Set.Iic T => brownianBridge B T s w)) inferInstance
    apply Measurable.comap_le
    have hm : Measurable
        (fun w => (B T w, fun s : Set.Iic T => brownianBridge B T s w)) :=
      comap_measurable _
    apply Measurable.of_eval
    intro s
    convert ((measurable_pi_apply s).comp (measurable_snd.comp hm)).add
      ((measurable_fst.comp hm).const_mul ((s : ℝ≥0) / (T : ℝ))) using 1
    funext w
    simp [brownianBridge]
  · let : MeasurableSpace Omega :=
      MeasurableSpace.comap (fun w (s : Set.Iic T) => B s w) inferInstance
    apply Measurable.comap_le
    have hm : Measurable (fun w (s : Set.Iic T) => B s w) := comap_measurable _
    have ht : Measurable (B T) := (measurable_pi_apply (⟨T, by simp⟩ : Set.Iic T)).comp hm
    apply ht.prodMk
    apply Measurable.of_eval
    intro s
    exact ((measurable_pi_apply s).comp hm).sub (ht.const_mul _)

end Problem367

end

end OAI
