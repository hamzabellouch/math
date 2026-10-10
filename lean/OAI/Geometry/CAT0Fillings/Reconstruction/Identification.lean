import Mathlib
import OAI.Geometry.CAT0Fillings.Reconstruction.Localization
import OAI.Geometry.CAT0Fillings.Reconstruction.ScalarCharts
import OAI.Geometry.CAT0Fillings.Reconstruction.ScalarKernel

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients BorelRestriction Slicing

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma chart_mass_compl_image_zero {k : ℕ} (C : IntegerChart X k)
    (hC : IsMetricCurrent C.action) : currentMassMeasure hC C.imageᶜ = 0 := by
  have he := C.restrictCurrent_image_eq hC C.measurableSet_image (subset_refl _)
  have hs := massMeasure_restrict_compl_zero hC C.measurableSet_image
  simpa only [he] using hs

theorem scalar_graph_restriction_eq_chart
    {Ts : ℕ → Functional X 1} {T : Functional X 1}
    (hTs : ∀ j, IsIntegral 1 (Ts j))
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    (M N : ℝ≥0) (hM : ∀ j, mass (Ts j) ≤ M)
    (hN : ∀ j, mass (boundarySucc (Ts j)) ≤ N)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π)))
    (hX : IsCAT0 X) {u : X → ℝ} {Ku : ℝ≥0} (hu : LipschitzWith Ku u)
    {D : Set ℝ} (hD : IsCompact D) {m : ℕ} (γ : D → Fin m → X)
    (hγ : ∀ j, ∃ L U : ℝ≥0, LipschitzWith L (fun t => γ t j) ∧
      AntilipschitzWith U (fun t => γ t j)) (a : Fin m → ℤ)
    (hbase : ∀ t j, u (γ t j) = t) (hinj : ∀ t, Function.Injective (γ t))
    (hrep : ∀ t : D, UnitRepresentation (superlevelSlice hT hB u t) a (γ t))
    (j : Fin m) :
    restrictCurrent hT (Set.range (fun t => γ t j)) =
      (scalarGraphChart hD (fun t => γ t j) (hγ j) (a j)).action := by
  classical
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
  let C := scalarGraphChart hD (fun t => γ t j) (hγ j) (a j)
  let E := Set.range (fun t => γ t j)
  have hγc (i : Fin m) : Continuous (fun t => γ t i) := (hγ i).choose_spec.choose_spec.1.continuous
  have hE : MeasurableSet E := (isCompact_range (hγc j)).measurableSet
  have hR := restrictCurrent_isMetricCurrent hT hE
  have hC : IsMetricCurrent C.action := C.action_isMetricCurrent
  obtain ⟨ht,hb,hI⟩ := integral_slice_tree_of_bounded_weak_limit hTs M N hM hN hlim hX
  have hI' : ∀ᵐ t : ℝ, IsIntegral 0 (superlevelSlice hT hB u t) := hI u Ku hu
  apply current_eq_on_scalar_graph (currentMassMeasure hR) hR hC
    (currentMassMeasure_controls hR) (currentMassMeasure hC) (currentMassMeasure_controls hC)
    hD (fun t => γ t j) (hγ j).choose_spec.choose_spec.1 hu (fun t => hbase t j)
    (massMeasure_restrict_compl_zero hT hE)
  · have he : C.image = E := scalarGraphChart_image hD _ (hγ j) (a j)
    simpa only [he] using chart_mass_compl_image_zero C hC
  intro b hb
  let f := E.indicator b
  have hf : Measurable f := hb.continuous.measurable.indicator hE
  obtain ⟨B,hBb⟩ := hb.2
  let B' : ℝ≥0 := ⟨max B 0,le_max_right _ _⟩
  have hfB (x : X) : |f x| ≤ B' := by
    by_cases hx : x ∈ E
    · exact (by simpa only [f,indicator_of_mem hx] using (show |b x| ≤ B' from (hBb x).trans (le_max_left B 0)))
    · simp only [f,indicator_of_notMem hx,abs_zero]
      exact B'.coe_nonneg
  have ha := superlevelSlice_borel_integral_of_bounded_weak_limit hTs hT hB M N hM hN hlim hX hu
    (fun z => Fin.elim0 z) (fun z => Fin.elim0 z) hf B' hfB
  have hp : Matrix.vecCons u (fun z => Fin.elim0 z) = fun _ : Fin 1 => u := by
    funext i
    exact Fin.cases rfl (fun z => Fin.elim0 z) i
  dsimp only [ActionIntegralAgreement] at ha
  rw [hp] at ha
  have hs := superlevelSlice_graph_action hT hB hu.continuous hI' hD γ hγc a hbase hinj hrep hb j
  rw [restrictCurrent_apply hT E ⟨hb,fun _ => ⟨Ku,hu⟩⟩,
    ←currentBorelAction_eq hT f (fun _ : Fin 1 => u),ha.2]
  change (∫ t, currentBorelAction (superlevelSlice hT hB u t) f (fun z => Fin.elim0 z)) = C.action b _
  rw [scalarGraphChart_base_action hD _ (hγ j) (a j) hu (fun t => hbase t j) hb]
  rw [←integral_indicator hD.measurableSet]
  apply integral_congr_ae
  filter_upwards [hs] with t ht
  rw [ht]
  by_cases htd : t ∈ D
  · simp only [dite_eq_left htd,indicator_of_mem htd,scalarGraphFunction]
  · simp only [dite_eq_right htd,indicator_of_notMem htd]

end CAT0Fillings.SliceReconstruction
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients BorelRestriction Slicing

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem joint_graph_restriction_eq_chart {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i))
    {D : Set (Euc k)} (hD : IsCompact D) {m : ℕ} (γ : D → Fin m → X)
    (hγ : ∀ j, ∃ L U : ℝ≥0, LipschitzWith L (fun t => γ t j) ∧
      AntilipschitzWith U (fun t => γ t j)) (a : Fin m → ℤ)
    (hbase : ∀ t j, coordinateMap π (γ t j) = t) (hinj : ∀ t, Function.Injective (γ t))
    (hrep : ∀ t : D, UnitRepresentation (fullSlice h π t) a (γ t))
    (j : Fin m) :
    restrictCurrent h.metric (Set.range (fun t => γ t j)) =
      (jointGraphChart hD (fun t => γ t j) (hγ j) (a j)).action := by
  classical
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
  let C := jointGraphChart hD (fun t => γ t j) (hγ j) (a j)
  let E := Set.range (fun t => γ t j)
  have hγc (i : Fin m) : Continuous (fun t => γ t i) := (hγ i).choose_spec.choose_spec.1.continuous
  have hE : MeasurableSet E := (isCompact_range (hγc j)).measurableSet
  have hR := restrictCurrent_isMetricCurrent h.metric hE
  have hC : IsMetricCurrent C.action := C.action_isMetricCurrent
  apply current_eq_on_joint_graph (currentMassMeasure hR) hR hC
    (currentMassMeasure_controls hR) (currentMassMeasure hC) (currentMassMeasure_controls hC)
    hD (fun t => γ t j) (hγ j).choose_spec.choose_spec.1 π (fun i => (hπ i).1)
    (fun t => hbase t j) (massMeasure_restrict_compl_zero h.metric hE)
  · have he : C.image = E := jointGraphChart_image hD _ (hγ j) (a j)
    simpa only [he] using chart_mass_compl_image_zero C hC
  intro ρ b hb
  rw [restrictCurrent_reindex h.metric (fun i => (hπ i).1) ρ
      (fun b hb => h.apply_reindex ⟨hb,fun i => (hπ i).1⟩ ρ) hE hb,
    C.action_reindex ⟨hb,fun i => (hπ i).1⟩ ρ,
    full_graph_restriction_base_action h hX π hπ hD γ hγ a hbase hinj hrep j hb]

end CAT0Fillings.SliceReconstruction
end

end OAI
