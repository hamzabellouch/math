import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.WeightedInitialSupport

namespace OAI

namespace BrownianForcing

open MeasureTheory Set

noncomputable def acceptedShiftMeasure {m : ℕ} (μ : Measure (FreeHeightSpace m))
    (v : FreeHeightSpace m) : Measure (FreeHeightSpace m) :=
  μ ⊓ μ.map (fun x => x-v)

noncomputable def acceptedShiftPair {m : ℕ} (μ : Measure (FreeHeightSpace m))
    (v : FreeHeightSpace m) : Measure (FreeHeightSpace m × FreeHeightSpace m) :=
  let J := (acceptedShiftMeasure μ v).map (fun x => (x,x+v))
  (1/2 : ENNReal) • (J+J.map Prod.swap)

noncomputable def metropolisShiftPair {m : ℕ} (μ : Measure (FreeHeightSpace m))
    (v : FreeHeightSpace m) : Measure (FreeHeightSpace m × FreeHeightSpace m) :=
  acceptedShiftPair μ v + (μ-(acceptedShiftPair μ v).map Prod.fst).map (fun x => (x,x))

end BrownianForcing

namespace BrownianForcing

open MeasureTheory Set

lemma acceptedShift_translate_le {m : ℕ} (μ : Measure (FreeHeightSpace m))
    (v : FreeHeightSpace m) :
    (acceptedShiftMeasure μ v).map (fun x => x+v) ≤ μ := by
  have hadd : Measurable (fun x : FreeHeightSpace m => x+v) := measurable_id.add_const v
  have hsub : Measurable (fun x : FreeHeightSpace m => x-v) := measurable_id.sub_const v
  have h := Measure.map_mono (μ := acceptedShiftMeasure μ v)
    (ν := μ.map (fun x => x-v)) inf_le_right hadd
  simpa only [Measure.map_map hadd hsub,
    Function.comp_def, sub_add_cancel, Measure.map_id'] using h

lemma acceptedShiftPair_fst {m : ℕ} (μ : Measure (FreeHeightSpace m))
    (v : FreeHeightSpace m) :
    (acceptedShiftPair μ v).map Prod.fst =
      (1/2:ENNReal) • (acceptedShiftMeasure μ v +
        (acceptedShiftMeasure μ v).map (fun x => x+v)) := by
  have hj : Measurable (fun x : FreeHeightSpace m => (x,x+v)) :=
    measurable_id.prodMk (measurable_id.add_const v)
  unfold acceptedShiftPair
  rw [Measure.map_smul _ measurable_fst.aemeasurable, Measure.map_add _ _ measurable_fst,
    Measure.map_map measurable_fst hj,
    Measure.map_map measurable_fst measurable_swap]
  rw [Measure.map_map (measurable_fst.comp measurable_swap) hj]
  simp only [Function.comp_def, Measure.map_id', Prod.fst_swap]

lemma acceptedShiftPair_fst_le {m : ℕ} (μ : Measure (FreeHeightSpace m))
    (v : FreeHeightSpace m) : (acceptedShiftPair μ v).map Prod.fst ≤ μ := by
  rw [acceptedShiftPair_fst]
  calc
    _ ≤ (1/2:ENNReal) • (μ+μ) := smul_le_smul_left _ (add_le_add inf_le_left (acceptedShift_translate_le μ v))
    _ = μ := by rw [← two_smul ENNReal μ, smul_smul]
                have hh : (1/2:ENNReal)*2=1 := by
                  rw [one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
                rw [hh, one_smul]

lemma acceptedShiftPair_swap {m : ℕ} (μ : Measure (FreeHeightSpace m))
    (v : FreeHeightSpace m) :
    (acceptedShiftPair μ v).map Prod.swap = acceptedShiftPair μ v := by
  unfold acceptedShiftPair
  rw [Measure.map_smul _ measurable_swap.aemeasurable, Measure.map_add _ _ measurable_swap,
    Measure.map_map measurable_swap measurable_swap]
  simp only [Function.comp_def, Prod.swap_swap, Measure.map_id']
  rw [add_comm]

lemma metropolisShiftPair_fst {m : ℕ} (μ : Measure (FreeHeightSpace m))
    [IsFiniteMeasure μ] (v : FreeHeightSpace m) :
    (metropolisShiftPair μ v).map Prod.fst = μ := by
  have hle := acceptedShiftPair_fst_le μ v
  have : IsFiniteMeasure ((acceptedShiftPair μ v).map Prod.fst) :=
    isFiniteMeasure_of_le μ hle
  have hd : Measurable (fun x : FreeHeightSpace m => (x,x)) := measurable_id.prodMk measurable_id
  unfold metropolisShiftPair
  rw [Measure.map_add _ _ measurable_fst, Measure.map_map measurable_fst hd]
  simp only [Function.comp_def, Measure.map_id']
  rw [add_comm, Measure.sub_add_cancel_of_le hle]

lemma metropolisShiftPair_swap {m : ℕ} (μ : Measure (FreeHeightSpace m))
    (v : FreeHeightSpace m) :
    (metropolisShiftPair μ v).map Prod.swap = metropolisShiftPair μ v := by
  have hd : Measurable (fun x : FreeHeightSpace m => (x,x)) := measurable_id.prodMk measurable_id
  unfold metropolisShiftPair
  rw [Measure.map_add _ _ measurable_swap, acceptedShiftPair_swap,
    Measure.map_map measurable_swap hd]
  rfl

lemma metropolisShiftPair_snd {m : ℕ} (μ : Measure (FreeHeightSpace m))
    [IsFiniteMeasure μ] (v : FreeHeightSpace m) :
    (metropolisShiftPair μ v).map Prod.snd = μ := by
  have h := congrArg (fun ν : Measure (FreeHeightSpace m × FreeHeightSpace m) => ν.map Prod.fst)
    (metropolisShiftPair_swap μ v)
  rw [Measure.map_map measurable_fst measurable_swap, metropolisShiftPair_fst] at h
  exact h

lemma metropolisShiftPair_probability {m : ℕ} (μ : Measure (FreeHeightSpace m))
    [IsProbabilityMeasure μ] (v : FreeHeightSpace m) :
    IsProbabilityMeasure (metropolisShiftPair μ v) := by
  constructor
  have h := congrArg (fun ν : Measure (FreeHeightSpace m) => ν univ)
    (metropolisShiftPair_fst μ v)
  simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,
    preimage_univ, measure_univ] using h

end BrownianForcing

end OAI
