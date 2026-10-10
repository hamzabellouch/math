import Mathlib
import OAI.Geometry.CAT0Fillings.Slicing.Superlevels
import OAI.Geometry.CAT0Fillings.Slices.Approximation

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.BorelRestriction
open Foundations MassMeasure BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
variable {k : ℕ} {T : Functional X k}

lemma restrictCurrent_controls_original (hT : IsMetricCurrent T) {E : Set X}
    (hE : MeasurableSet E) : Controls (restrictCurrent hT E) (currentMassMeasure hT) := by
  intro b π hb hπ
  exact (restrictCurrent_controls hT hE b π hb hπ).trans
    (integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall fun _ => abs_nonneg _) (integrable_boundedLip _ hb).abs)

lemma borelAction_restriction (hT : IsMetricCurrent T) {E : Set X} (hE : MeasurableSet E)
    {f : X → ℝ} (hf : Integrable f (currentMassMeasure hT))
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    borelAction (currentMassMeasure hT) (restrictCurrent_isMetricCurrent hT hE) f π =
      borelAction (currentMassMeasure hT) hT (E.indicator f) π := by
  let μ := currentMassMeasure hT
  let hR := restrictCurrent_isMetricCurrent hT hE
  have hc := restrictCurrent_controls_original hT hE
  obtain ⟨g,hg⟩ := exists_lipschitz_approximation μ hf
  have hlim := borelAction_tendsto μ hR hc hf (fun n => integrable_boundedLip μ (g n).property) hg π hπ
  have hind : Tendsto (fun n => ∫ x, |E.indicator (g n).val x - E.indicator f x| ∂μ) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _) (fun n => ?_) hg
    apply integral_mono ((integrable_boundedLip μ (g n).property).indicator hE |>.sub (hf.indicator hE) |>.abs)
      ((integrable_boundedLip μ (g n).property).sub hf).abs
    intro x
    by_cases hx : x ∈ E
    · simp only [Pi.sub_apply,indicator_of_mem hx,le_refl]
    · simp only [Pi.sub_apply,indicator_of_notMem hx,sub_self,abs_zero]
      exact abs_nonneg _
  have hlim' := borelAction_tendsto μ hT (currentMassMeasure_controls hT) (hf.indicator hE)
    (fun n => (integrable_boundedLip μ (g n).property).indicator hE) hind π hπ
  have he (n : ℕ) : borelAction μ hR (g n).val π = borelAction μ hT (E.indicator (g n).val) π := by
    rw [borelAction_eq μ hR hc ⟨(g n).property,hπ⟩,restrictCurrent_apply hT E ⟨(g n).property,hπ⟩]
  simp only [he] at hlim
  exact tendsto_nhds_unique hlim hlim'

lemma restrictCurrent_restrict (hT : IsMetricCurrent T) {E F : Set X}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    restrictCurrent (restrictCurrent_isMetricCurrent hT hE) F = restrictCurrent hT (E ∩ F) := by
  let hR := restrictCurrent_isMetricCurrent hT hE
  have hμR : currentMassMeasure hR ≤ currentMassMeasure hT :=
    currentMassMeasure_le hR (restrictCurrent_controls_original hT hE)
  funext b π
  by_cases hab : Admissible b π
  · rw [restrictCurrent_apply hR F hab,restrictCurrent_apply hT (E∩F) hab,
      borelAction_independent _ hR (currentMassMeasure_controls hR)
        (restrictCurrent_controls_original hT hE)
        ((integrable_boundedLip _ hab.1).indicator hF)
        ((integrable_boundedLip _ hab.1).indicator hF) π hab.2,
      borelAction_restriction hT hE ((integrable_boundedLip _ hab.1).indicator hF) π hab.2]
    congr 1
    ext x
    by_cases hxE : x ∈ E <;> by_cases hxF : x ∈ F <;> simp [hxE,hxF]
  · simp only [restrictCurrent,ite_eq_right hab]

lemma restrictCurrent_eq_self_of_mass_compl_zero (hT : IsMetricCurrent T) {E : Set X}
    (hE : MeasurableSet E) (hμ : currentMassMeasure hT Eᶜ = 0) : restrictCurrent hT E = T := by
  funext b π
  by_cases hab : Admissible b π
  · rw [restrictCurrent_apply hT E hab]
    have he : E.indicator b =ᵐ[currentMassMeasure hT] b := by
      filter_upwards [show ∀ᵐ x ∂currentMassMeasure hT, x ∈ E from
        (ae_mem_iff_measure_eq hE.nullMeasurableSet).mpr (by
          simpa only [hμ,add_zero] using
            measure_add_measure_compl (μ := currentMassMeasure hT) hE)] with x hx
      exact indicator_of_mem hx _
    rw [borelAction_congr_ae _ hT he,borelAction_eq _ hT (currentMassMeasure_controls hT) hab]
  · simp only [restrictCurrent,ite_eq_right hab,hT.offDomain b π hab]

lemma massMeasure_restrict_compl_zero (hT : IsMetricCurrent T) {E : Set X}
    (hE : MeasurableSet E) :
    currentMassMeasure (restrictCurrent_isMetricCurrent hT hE) Eᶜ = 0 := by
  rw [restriction_massMeasure hT hE,Measure.restrict_apply hE.compl,compl_inter_self,measure_empty]

end CAT0Fillings.BorelRestriction
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients BorelRestriction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X]

lemma borelAction_mul_zero_of_lip {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {w : X → ℝ} (hw : BoundedLip w)
    (hz : ∀ b π, Admissible b π → T (fun x => w x * b x) π = 0)
    {f : X → ℝ} (hf : Integrable f (currentMassMeasure hT))
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    borelAction (currentMassMeasure hT) hT (fun x => w x * f x) π = 0 := by
  let μ := currentMassMeasure hT
  obtain ⟨B,hB⟩ := hw.2
  have hbnd : ∀ᵐ x ∂μ, ‖w x‖ ≤ B := Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using hB x
  have hfi : Integrable (fun x => w x * f x) μ := by
    simpa only [mul_comm] using hf.mul_bdd hw.continuous.aestronglyMeasurable hbnd
  obtain ⟨g,hg⟩ := exists_lipschitz_approximation μ hf
  have hgi n : Integrable (fun x => w x * (g n).val x) μ :=
    integrable_boundedLip μ (hw.mul (g n).property)
  have hlim : Tendsto (fun n => ∫ x, |w x * (g n).val x - w x * f x| ∂μ) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => integral_nonneg fun x => abs_nonneg _) (fun n => ?_)
      (by simpa only [mul_zero] using hg.const_mul B)
    rw [←integral_const_mul]
    apply integral_mono ((hgi n).sub hfi).abs (((integrable_boundedLip μ (g n).property).sub hf).abs.const_mul B)
    intro x
    change |w x * (g n).val x - w x * f x| ≤ B * |(g n).val x - f x|
    rw [←mul_sub,abs_mul]
    exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _)
  have ht := borelAction_tendsto μ hT (currentMassMeasure_controls hT) hfi hgi hlim π hπ
  have he n : borelAction μ hT (fun x => w x * (g n).val x) π = 0 := by
    rw [borelAction_eq μ hT (currentMassMeasure_controls hT) ⟨hw.mul (g n).property,hπ⟩]
    exact hz _ _ ⟨(g n).property,hπ⟩
  simp only [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

lemma massMeasure_nonzero_zero_of_mul_zero {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {w : X → ℝ} (hw : BoundedLip w)
    (hz : ∀ b π, Admissible b π → T (fun x => w x * b x) π = 0) :
    currentMassMeasure hT {x | w x ≠ 0} = 0 := by
  let E (n : ℕ) : Set X := {x | 1 / (n+1:ℝ) ≤ |w x|}
  have hE n : MeasurableSet (E n) := measurableSet_le measurable_const hw.continuous.abs.measurable
  have hzero n : restrictCurrent hT (E n) = 0 := by
    funext b π
    by_cases hab : Admissible b π
    · obtain ⟨B,hB⟩ := hab.1.2
      let f : X → ℝ := (E n).indicator (fun x => b x / w x)
      have hfm : Measurable f := (hab.1.continuous.measurable.div hw.continuous.measurable).indicator (hE n)
      have hfB x : ‖f x‖ ≤ max B 0 * (n+1:ℝ) := by
        by_cases hx : x ∈ E n
        · have hw0 : 0 < |w x| := lt_of_lt_of_le (by positivity : (0:ℝ) < 1/(n+1:ℝ)) hx
          simp only [f,indicator_of_mem hx,Real.norm_eq_abs,abs_div]
          apply (div_le_iff₀ hw0).mpr
          have hc : (1:ℝ) ≤ (n+1:ℝ)*|w x| := by
            simpa only [mul_comm] using (div_le_iff₀ (by positivity : (0:ℝ)<n+1)).mp hx
          calc |b x| ≤ max B 0 := (hB x).trans (le_max_left _ _)
            _ ≤ max B 0 * ((n+1:ℝ)*|w x|) := le_mul_of_one_le_right (le_max_right _ _) hc
            _ = _ := by ring
        · simp only [f,indicator_of_notMem hx,norm_zero]
          positivity
      have hfi : Integrable f (currentMassMeasure hT) :=
        (integrable_const (max B 0 * (n+1:ℝ))).mono' hfm.aestronglyMeasurable (Eventually.of_forall hfB)
      rw [restrictCurrent_apply hT (E n) hab]
      have he : (E n).indicator b = fun x => w x * f x := by
        funext x
        by_cases hx : x ∈ E n
        · have hw0 : w x ≠ 0 := abs_pos.mp (lt_of_lt_of_le (by positivity : (0:ℝ)<1/(n+1:ℝ)) hx)
          simp only [f,indicator_of_mem hx]
          field_simp
        · simp [f,hx]
      rw [he]
      exact borelAction_mul_zero_of_lip hT hw hz hfi π hab.2
    · simp [restrictCurrent,hab]
  have hμ n : currentMassMeasure hT (E n) = 0 := by
    have hm := restriction_mass hT (hE n)
    rw [hzero n] at hm
    have hm0 : mass (0 : Functional X k) = 0 := mass_zero k
    rw [hm0] at hm
    exact (ENNReal.toReal_eq_zero_iff _).mp hm.symm |>.resolve_right (measure_ne_top _ _)
  have hsub : {x | w x ≠ 0} ⊆ ⋃ n, E n := by
    intro x hx
    have hw0 : 0 < |w x| := abs_pos.mpr hx
    obtain ⟨n,hn⟩ := exists_nat_gt (1/|w x|)
    apply mem_iUnion.mpr
    refine ⟨n,?_⟩
    change 1 / (n+1:ℝ) ≤ |w x|
    apply (div_le_iff₀ (by positivity : (0:ℝ)<n+1)).mpr
    have hh := (div_lt_iff₀ hw0).mp hn
    nlinarith
  exact measure_mono_null hsub (measure_iUnion_null fun n => hμ n)

lemma mul_action_zero_of_massMeasure_nonzero_zero {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {w : X → ℝ} (hw : BoundedLip w)
    (hz : currentMassMeasure hT {x | w x ≠ 0} = 0)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π) :
    T (fun x => w x * b x) π = 0 := by
  have he : (fun x => w x * b x) =ᵐ[currentMassMeasure hT] 0 := by
    filter_upwards [show ∀ᵐ x ∂currentMassMeasure hT, w x = 0 from ae_iff.mpr hz] with x hx
    simp [hx]
  rw [←borelAction_eq _ hT (currentMassMeasure_controls hT) ⟨hw.mul hab.1,hab.2⟩,
    borelAction_congr_ae _ hT he,borelAction_of_integrable _ hT (integrable_zero X ℝ _) π hab.2]
  simp

lemma boundary_mul_zero_of_massMeasure {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) {w : X → ℝ} (hw : BoundedLip w)
    (hz : currentMassMeasure hT {x | w x ≠ 0} = 0)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π) :
    boundarySucc T (fun x => w x * b x) π = 0 := by
  let E : Set X := {x | w x = 0}
  have hE : MeasurableSet E := hw.continuous.measurable (measurableSet_singleton 0)
  have he : (fun _ : X => (1:ℝ)) =ᵐ[currentMassMeasure hT] E.indicator (fun _ => (1:ℝ)) := by
    filter_upwards [show ∀ᵐ x ∂currentMassMeasure hT, w x = 0 from ae_iff.mpr hz] with x hx
    exact (indicator_of_mem (show x ∈ E from hx) (fun _ : X => (1:ℝ))).symm
  let σ := Matrix.vecCons (fun x => w x * b x) π
  have hσ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (σ j) :=
    fun j => Fin.cases (hw.mul hab.1).1 (fun i => hab.2 i) j
  rw [boundarySucc,ite_eq_left ⟨hw.mul hab.1,hab.2⟩]
  change T (fun _ => 1) σ = 0
  rw [←borelAction_eq _ hT (currentMassMeasure_controls hT) ⟨BoundedLip.const 1,hσ⟩,
    borelAction_congr_ae _ hT he]
  apply borelAction_locality_level _ hT (currentMassMeasure_controls hT)
    ((integrable_const (1:ℝ)).indicator hE) σ hσ 0 0
  intro x hx
  have hxE : x ∈ E := mem_of_indicator_ne_zero hx
  change w x * b x = 0
  rw [show w x = 0 from hxE,zero_mul]

lemma massMeasure_boundary_nonzero_zero {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    {w : X → ℝ} (hw : BoundedLip w)
    (hz : currentMassMeasure hT {x | w x ≠ 0} = 0) :
    currentMassMeasure hB {x | w x ≠ 0} = 0 := by
  apply massMeasure_nonzero_zero_of_mul_zero hB hw
  intro b π hab
  exact boundary_mul_zero_of_massMeasure hT hw hz hab

lemma massMeasure_restrict_nonzero_zero {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {E : Set X} (hE : MeasurableSet E)
    {w : X → ℝ} (hz : currentMassMeasure hT {x | w x ≠ 0} = 0) :
    currentMassMeasure (restrictCurrent_isMetricCurrent hT hE) {x | w x ≠ 0} = 0 := by
  rw [restriction_massMeasure hT hE]
  exact le_antisymm ((Measure.restrict_le_self _).trans_eq hz) bot_le

lemma massMeasure_superlevelSlice_nonzero_zero {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} (hu : Continuous u) (t : ℝ)
    (hS : IsMetricCurrent (superlevelSlice hT hB u t))
    {w : X → ℝ} (hw : BoundedLip w)
    (hz : currentMassMeasure hT {x | w x ≠ 0} = 0) :
    currentMassMeasure hS {x | w x ≠ 0} = 0 := by
  have hE : MeasurableSet {x | t < u x} := measurableSet_lt measurable_const hu.measurable
  have hBT := massMeasure_boundary_nonzero_zero hT hB hw hz
  have hRT := massMeasure_restrict_nonzero_zero hT hE hz
  have hRB := massMeasure_restrict_nonzero_zero hB hE hBT
  apply massMeasure_nonzero_zero_of_mul_zero hS hw
  intro b π hab
  change restrictCurrent hB _ (fun x => w x * b x) π -
    boundarySucc (restrictCurrent hT _) (fun x => w x * b x) π = 0
  rw [mul_action_zero_of_massMeasure_nonzero_zero (restrictCurrent_isMetricCurrent hB hE) hw hRB hab,
    boundary_mul_zero_of_massMeasure (restrictCurrent_isMetricCurrent hT hE) hw hRT hab,sub_self]

end CAT0Fillings.Slicing
end

end OAI
