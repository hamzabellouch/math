import OAI.Analysis.CircleDomains.Modulus.GridIncidence
import OAI.Analysis.CircleDomains.Selection.LusinInput

namespace OAI

/-!
# Transferring almost-everywhere compatibility to actual grid choices

Independent shifts for distinct labels have the required finite product law.
Each shifted grid level has a law absolutely continuous with respect to Haar
measure on the circle. Consequently every completed-product null failure
set remains null for actual grid tuples. Repeated levels of one label are
not treated as independent; the tuple map explicitly requires distinct labels.
-/

open Set MeasureTheory Function ProbabilityTheory

namespace CircleDomainRigidity.FiniteTransfer

/-- Absolute continuity passes to the finite products needed for level laws. -/
theorem absolutelyContinuous_pi_fin {T : Type*} [MeasurableSpace T] :
    ∀ (n : ℕ) (μ ν : Fin n → Measure T) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)],
      (∀ i, μ i ≪ ν i) → Measure.pi μ ≪ Measure.pi ν := by
  intro n
  induction n with
  | zero =>
      intro μ ν _ _ _
      rw [Measure.pi_of_empty μ, Measure.pi_of_empty ν]
  | succ n ih =>
      intro μ ν _ _ h
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => T) 0
      have hμ := measurePreserving_piFinSuccAbove μ (0 : Fin (n + 1))
      have hν := measurePreserving_piFinSuccAbove ν (0 : Fin (n + 1))
      have htail := ih (fun i => μ ((0 : Fin (n + 1)).succAbove i))
        (fun i => ν ((0 : Fin (n + 1)).succAbove i))
        (fun i => h ((0 : Fin (n + 1)).succAbove i))
      have hprod := (h 0).prod htail
      have hback := hprod.map e.symm.measurable
      rw [← hμ.map_eq, ← hν.map_eq] at hback
      change ((Measure.pi μ).map e).map e.symm ≪ ((Measure.pi ν).map e).map e.symm at hback
      have heid : e.symm ∘ e = id := by funext x; exact e.symm_apply_apply x
      simpa only [Measure.map_map e.symm.measurable e.measurable, heid, Measure.map_id] using hback

/-- A uniform shift on a subinterval of a period, followed by any circle
translation, has a Haar-absolutely-continuous law. -/
theorem quasiMeasurePreserving_translated_grid_level {h : ℝ}
    (_hh : 0 < h) (hsmall : h ≤ 1) (c : ℝ) :
    Measure.QuasiMeasurePreserving (fun θ : ℝ => ((θ + c : ℝ) : UnitAddCircle))
      (shiftLaw h) volume := by
  have hle : volume.restrict (Icc (0 : ℝ) h) ≤ volume.restrict (Icc (0 : ℝ) 1) :=
    Measure.restrict_mono (Icc_subset_Icc_right hsmall) le_rfl
  have hac : shiftLaw h ≪ volume.restrict (Ioc (0 : ℝ) (0 + 1)) := by
    rw [shiftLaw_eq, zero_add, restrict_Ioc_eq_restrict_Icc]
    exact (Measure.absolutelyContinuous_of_le hle).smul_left _
  have hquot := (AddCircle.measurePreserving_mk (T := (1 : ℝ)) 0).quasiMeasurePreserving.mono_left hac
  have htranslate := (measurePreserving_add_right (volume : Measure UnitAddCircle)
    (c : UnitAddCircle)).quasiMeasurePreserving
  convert htranslate.comp hquot using 1
  ext θ
  simp only [Function.comp_apply, AddCircle.coe_add]

/-- Finite products of the translated grid levels remain absolutely
continuous with respect to independent Haar measure. -/
theorem quasiMeasurePreserving_grid_levels {n : ℕ} {h : ℝ}
    (hh : 0 < h) (hsmall : h ≤ 1) (c : Fin n → ℝ) :
    Measure.QuasiMeasurePreserving
      (fun θ : Fin n → ℝ => fun i => ((θ i + c i : ℝ) : UnitAddCircle))
      (Measure.pi (fun _ : Fin n => shiftLaw h))
      (Measure.pi (fun _ : Fin n => volume)) := by
  let := shiftLaw_isProbabilityMeasure hh
  have hf i := quasiMeasurePreserving_translated_grid_level hh hsmall (c i)
  refine ⟨measurable_pi_iff.mpr (fun i => (hf i).measurable.comp (measurable_pi_apply i)), ?_⟩
  rw [Measure.pi_map_pi (fun i => (hf i).aemeasurable)]
  exact absolutelyContinuous_pi_fin n _ _ (fun i => (hf i).absolutelyContinuous)

/-- Selecting distinct labels from an independent finite shift family
preserves their product law. -/
theorem measurePreserving_distinct_grid_labels {m n : ℕ} {h : ℝ}
    (hh : 0 < h) (labels : Fin n → Fin m) (hinj : Injective labels) :
    MeasurePreserving (fun θ : Fin m → ℝ => fun j => θ (labels j))
      (Measure.pi (fun _ : Fin m => shiftLaw h))
      (Measure.pi (fun _ : Fin n => shiftLaw h)) := by
  let := shiftLaw_isProbabilityMeasure hh
  have hind := (iIndepFun_pi (μ := fun _ : Fin m => shiftLaw h)
    (X := fun _ => id) (fun _ => aemeasurable_id)).precomp hinj
  refine ⟨measurable_pi_iff.mpr (fun j => measurable_pi_apply (labels j)), ?_⟩
  have hmap := hind.map_fun_eq_pi_map (fun j => (measurable_pi_apply (labels j)).aemeasurable)
  simpa only [(measurePreserving_eval (fun _ : Fin m => shiftLaw h) _).map_eq] using hmap

/-- Every completed-product null event is avoided almost surely by a
chosen tuple of actual grid levels on distinct labels. Offsets may be
any lattice offsets, since the proof allows every real translation. -/
theorem ae_grid_tuple_avoids_null_event {m d : ℕ} {h : ℝ}
    (hh : 0 < h) (hsmall : h ≤ 1) (labels : Fin (d + 1) → Fin m)
    (hinj : Injective labels) (c : Fin (d + 1) → ℝ)
    (E : Set (UnitAddCircle × (Fin d → UnitAddCircle)))
    (hE : (volume.prod (Measure.pi (fun _ : Fin d => volume))) E = 0) :
    ∀ᵐ θ ∂Measure.pi (fun _ : Fin m => shiftLaw h),
      (((θ (labels 0) + c 0 : ℝ) : UnitAddCircle),
        fun i : Fin d => ((θ (labels i.succ) + c i.succ : ℝ) : UnitAddCircle)) ∉ E := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => UnitAddCircle) 0
  have he := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (d + 1) => (volume : Measure UnitAddCircle)) 0).quasiMeasurePreserving
  have hq := he.comp ((quasiMeasurePreserving_grid_levels hh hsmall c).comp
    (measurePreserving_distinct_grid_labels hh labels hinj).quasiMeasurePreserving)
  have hn := hq.preimage_null hE
  change (Measure.pi (fun _ : Fin m => shiftLaw h))
    {θ | (((θ (labels 0) + c 0 : ℝ) : UnitAddCircle),
      fun i : Fin d => ((θ (labels ((0 : Fin (d + 1)).succAbove i)) +
        c ((0 : Fin (d + 1)).succAbove i) : ℝ) : UnitAddCircle)) ∈ E} = 0 at hn
  apply ae_iff.mpr
  simpa only [not_not, ofPred_mem_eq, Fin.succAbove_zero] using hn

end CircleDomainRigidity.FiniteTransfer

end OAI
