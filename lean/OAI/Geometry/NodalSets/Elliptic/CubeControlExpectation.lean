import OAI.Geometry.NodalSets.Elliptic.AnchoredCubeBound

namespace OAI

namespace Yau.Analysis
open MeasureTheory Set Function
open scoped ENNReal
noncomputable section
variable {ι Ω : Type*} [DecidableEq ι] [MeasurableSpace Ω]

lemma measurable_coordinate_update {f : Ω → (ι → ℝ)} {g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g) (i : ι) :
    Measurable (fun a ↦ update (f a) i (g a)) := by
  apply Measurable.of_eval
  intro j
  by_cases h : j = i
  · subst j; simpa only [update_self] using hg
  · simpa only [update_of_ne h, Function.comp_def] using (measurable_pi_apply j).comp hf

lemma cubeControl_measurable (f : Ω → List ι → (ι → ℝ) → ℝ)
    (hf : ∀ ds, Measurable (fun z : Ω × (ι → ℝ) ↦ f z.1 ds z.2))
    (is ds : List ι) :
    Measurable (fun z : Ω × (ι → ℝ) ↦ cubeControl (f z.1) is ds z.2) := by
  induction is generalizing ds with
  | nil => exact (hf ds).enorm
  | cons i is ih =>
    change Measurable (fun z : Ω × (ι → ℝ) ↦
      cubeControl (f z.1) is ds (update z.2 i 0) +
        ∫⁻ t in Icc (-1:ℝ) 1, cubeControl (f z.1) is (i::ds) (update z.2 i t))
    apply Measurable.add
    · exact (ih ds).comp (measurable_fst.prodMk (measurable_coordinate_update measurable_snd measurable_const i))
    · apply Measurable.lintegral_prod_right
      exact (ih (i::ds)).comp ((measurable_fst.fst).prodMk
        (measurable_coordinate_update measurable_fst.snd measurable_snd i))

lemma cubeControl_measurable_at (f : Ω → List ι → (ι → ℝ) → ℝ)
    (hf : ∀ ds, Measurable (fun z : Ω × (ι → ℝ) ↦ f z.1 ds z.2))
    (is ds : List ι) (x : ι → ℝ) :
    Measurable (fun a ↦ cubeControl (f a) is ds x) :=
  (cubeControl_measurable f hf is ds).comp (measurable_id.prodMk measurable_const)

lemma cubeControl_lintegral_le (f : Ω → List ι → (ι → ℝ) → ℝ)
    (hf : ∀ ds, Measurable (fun z : Ω × (ι → ℝ) ↦ f z.1 ds z.2))
    (μ : Measure Ω) [SFinite μ] (d : ℕ) (C : ℝ≥0∞)
    (hb : ∀ ds, ds.length ≤ d → ∀ x, InUnitCube x →
      (∫⁻ a, ‖f a ds x‖ₑ ∂μ) ≤ C)
    (is ds : List ι) (hlen : ds.length + is.length ≤ d)
    (x : ι → ℝ) (hx : InUnitCube x) :
    (∫⁻ a, cubeControl (f a) is ds x ∂μ) ≤ 3^is.length * C := by
  induction is generalizing ds x with
  | nil => simpa [cubeControl] using hb ds (by simpa using hlen) x hx
  | cons i is ih =>
    have hm (ds' : List ι) (y : ι → ℝ) :
        Measurable (fun a ↦ cubeControl (f a) is ds' y) :=
      (cubeControl_measurable f hf is ds').comp (measurable_id.prodMk measurable_const)
    have hj : Measurable (fun z : Ω × ℝ ↦
        cubeControl (f z.1) is (i::ds) (update x i z.2)) :=
      (cubeControl_measurable f hf is (i::ds)).comp
        (measurable_fst.prodMk (measurable_coordinate_update measurable_const measurable_snd i))
    simp only [cubeControl]
    rw [lintegral_add_left (hm ds _), lintegral_lintegral_swap hj.aemeasurable]
    calc
      _ ≤ 3^is.length*C + ∫⁻ t in Icc (-1:ℝ) 1, 3^is.length*C := by
        apply add_le_add (ih ds (by simp_all only [List.length_cons]; omega) _
          (inUnitCube_update hx i (by norm_num)))
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
        exact ih (i::ds) (by simp_all only [List.length_cons]; omega) _
          (inUnitCube_update hx i (abs_le.mpr ht))
      _ = _ := by
        simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
          List.length_cons, pow_succ]
        norm_num
        ring

end
end Yau.Analysis

end OAI
