import Mathlib
import OAI.Geometry.CAT0Fillings.Slices.Carriers
import OAI.Geometry.CAT0Fillings.Slices.FullSlices

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients BorelRestriction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

omit [MeasurableSpace X] [BorelSpace X] [Nonempty X] in
lemma boundedLip_sub_const [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    {u : X → ℝ} (hu : BoundedLip u) (t : ℝ) :
    BoundedLip (fun x => u x-t) :=
  boundedLip_of_lipschitz (hu.1.choose_spec.sub (LipschitzWith.const t))

omit [Nonempty X] in
lemma weightedCurrent_boundedLip_isMetricCurrent [Nonempty X] {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {w : X → ℝ} (hw : BoundedLip w) :
    IsMetricCurrent (weightedCurrent (currentMassMeasure hT) hT w) := by
  obtain ⟨B,hB⟩ := hw.2
  apply weightedCurrent_isMetricCurrent _ hT (currentMassMeasure_controls hT)
    (integrable_boundedLip _ hw) (M := ⟨max B 0,le_max_right _ _⟩)
  exact Eventually.of_forall fun x => (hB x).trans (le_max_left _ _)

omit [Nonempty X] in
lemma weightedCurrent_boundedLip_apply [Nonempty X] {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {w : X → ℝ} (hw : BoundedLip w)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π) :
    weightedCurrent (currentMassMeasure hT) hT w b π = T (fun x => w x * b x) π := by
  rw [weightedCurrent,ite_eq_left hab]
  exact borelAction_eq _ hT (currentMassMeasure_controls hT) ⟨hw.mul hab.1,hab.2⟩

lemma NormalApprox.metric {k : ℕ} {T : Functional X k} (h : NormalApprox k T) : IsMetricCurrent T := by
  cases k with
  | zero => exact h.integral_zero.1
  | succ k => exact h.normal.1

lemma massMeasure_normalSlice_nonzero_zero {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) {u : X → ℝ} (hu : Continuous u) (t : ℝ)
    {w : X → ℝ} (hw : BoundedLip w)
    (hz : currentMassMeasure h.metric {x | w x ≠ 0} = 0) :
    currentMassMeasure (normalSlice_approx h u t).metric {x | w x ≠ 0} = 0 := by
  classical
  by_cases hs : NormalApprox k (superlevelSlice h.normal.1 h.normal.2 u t)
  · have he : normalSlice h u t = superlevelSlice h.normal.1 h.normal.2 u t := ite_eq_left hs
    apply massMeasure_nonzero_zero_of_mul_zero _ hw
    intro b π hab
    rw [he]
    exact mul_action_zero_of_massMeasure_nonzero_zero hs.metric hw
      (massMeasure_superlevelSlice_nonzero_zero h.normal.1 h.normal.2 hu t hs.metric hw hz) hab
  · have he : normalSlice h u t = 0 := ite_eq_right hs
    apply massMeasure_nonzero_zero_of_mul_zero _ hw
    intro b π hab
    rw [he]
    rfl

lemma massMeasure_fullSlice_nonzero_zero {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (π : Fin k → X → ℝ) (hπ : ∀ i, Continuous (π i))
    {w : X → ℝ} (hw : BoundedLip w)
    (hz : currentMassMeasure h.metric {x | w x ≠ 0} = 0) (z : Euc k) :
    currentMassMeasure (fullSlice_approx h π z).metric {x | w x ≠ 0} = 0 := by
  induction k with
  | zero => exact hz
  | succ k ih =>
    exact ih (normalSlice_approx h (π 0) (Prism.split k z).1) (Fin.tail π)
      (fun i => hπ i.succ) (massMeasure_normalSlice_nonzero_zero h (hπ 0) _ hw hz) (Prism.split k z).2

lemma ae_superlevelSlice_weighted_integral {k : ℕ} {T : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π)
    {φ : ℝ → ℝ} (hφ : BoundedLip (φ ∘ u)) :
    ∀ᵐ t : ℝ, superlevelSlice hT.1 hT.2.2.1 u t (fun x => φ (u x)*b x) π =
      φ t * superlevelSlice hT.1 hT.2.2.1 u t b π := by
  obtain ⟨S,G,hG,hG0,hS,hGI,hact,hweight⟩ := integerRectifiable_scalar_coarea hT.1 hT.2.1 hX hK
  filter_upwards [ae_superlevelSlice_eq_coarea hT.1 hT.2.1 hT.2.2.1
    (boundedLip_of_lipschitz hK) (hS.mono fun _ ht => ht.1) hact hweight,hweight b π hab φ hφ] with t he ht
  simpa only [he] using ht

lemma NormalApprox.ae_superlevelSlice_weighted {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π)
    {φ : ℝ → ℝ} (hφ : BoundedLip (φ ∘ u)) :
    ∀ᵐ t : ℝ, superlevelSlice h.normal.1 h.normal.2 u t (fun x => φ (u x)*b x) π =
      φ t * superlevelSlice h.normal.1 h.normal.2 u t b π := by
  have hcopy := h
  obtain ⟨C,Ts,hTs,hM,hN,hlim⟩ := hcopy
  obtain ⟨ψ,hψ,μs,νs,μ,ν,hμs,hμ,hνs,hν,hμlim,hνlim⟩ :=
    exists_joint_weak_controlling_subsequence (fun j => (hTs j).1)
      (fun j => (hTs j).2.2.1) C C hM hN hlim (boundarySucc_weak_limit hlim)
  have hweak := ae_superlevelSlice_weak_tendsto (fun j => (hTs (ψ j)).1) h.normal.1
    (fun j => (hTs (ψ j)).2.2.1) h.normal.2 μs νs μ ν hμs hμ hνs hν hμlim hνlim
    (fun b π => (hlim b π).comp hψ.tendsto_atTop) (boundedLip_of_lipschitz hK)
  have ht := ae_all_iff.mpr (fun j => ae_superlevelSlice_weighted_integral (hTs (ψ j)) hX hK hab hφ)
  filter_upwards [hweak,ht] with t hwt he
  have hl := hwt (fun x => φ (u x)*b x) π
  have hr := (hwt b π).const_mul (φ t)
  simp only [he] at hl
  exact tendsto_nhds_unique hl hr

lemma ae_normalSlice_mul_level {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} (hu : BoundedLip u)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π) :
    ∀ᵐ t : ℝ, normalSlice h u t (fun x => (u x-t)*b x) π = 0 := by
  have hs := h.ae_superlevelSlice_weighted hX hu.1.choose_spec hab
    (φ := id) (by simpa only [Function.comp_def,id_eq] using hu)
  filter_upwards [ae_normalSlice_eq h hX hu.1.choose_spec,hs] with t he ht
  have hlin := (normalSlice_approx h u t).metric.linearFirst (fun x => u x*b x) b π 1 (-t) (hu.mul hab.1) hab.1 hab.2
  have hw : (fun x => 1*(u x*b x)+ -t*b x) = (fun x => (u x-t)*b x) := by funext x;ring
  rw [hw] at hlin
  rw [hlin,he]
  simp only [id_eq] at ht
  rw [ht]
  simp only [one_mul]
  ring

theorem ae_normalSlice_mass_level {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} (hu : BoundedLip u) :
    ∀ᵐ t : ℝ, currentMassMeasure (normalSlice_approx h u t).metric {x | u x ≠ t} = 0 := by
  let W (t : ℝ) := weightedCurrent (currentMassMeasure (normalSlice_approx h u t).metric)
    (normalSlice_approx h u t).metric (fun x => u x-t)
  have hW t : IsMetricCurrent (W t) :=
    weightedCurrent_boundedLip_isMetricCurrent _ (boundedLip_sub_const hu t)
  have he : ∀ᵐ t : ℝ, W t = (0 : Functional X k) := by
    apply ae_eq_of_ae_test_eq volume (Eventually.of_forall hW) (Eventually.of_forall fun _ => isMetricCurrent_zero k)
    intro b π hab
    filter_upwards [ae_normalSlice_mul_level h hX hu hab] with t ht
    exact (weightedCurrent_boundedLip_apply _ (boundedLip_sub_const hu t) hab).trans ht
  filter_upwards [he] with t ht
  have hh : currentMassMeasure (normalSlice_approx h u t).metric {x | u x-t ≠ 0} = 0 := by
    apply massMeasure_nonzero_zero_of_mul_zero _ (boundedLip_sub_const hu t)
    intro b π hab
    rw [←weightedCurrent_boundedLip_apply (normalSlice_approx h u t).metric (boundedLip_sub_const hu t) hab]
    exact congrFun (congrFun ht b) π
  simpa only [sub_ne_zero] using hh

end CAT0Fillings.Slicing
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients BorelRestriction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma level_eval_of_carrier {T : Functional X 0} (hT : IsMetricCurrent T)
    {u : X → ℝ} (hu : BoundedLip u) (t : ℝ)
    (hz : currentMassMeasure hT {x | u x ≠ t} = 0)
    {b : X → ℝ} (hb : BoundedLip b) (σ : Fin 0 → X → ℝ) :
    T (fun x => u x*b x) σ = t*T b σ := by
  have hh := mul_action_zero_of_massMeasure_nonzero_zero hT (boundedLip_sub_const hu t)
    (by simpa only [sub_ne_zero] using hz) (show Admissible b σ from ⟨hb,fun i => Fin.elim0 i⟩)
  have hl := hT.linearFirst (fun x => u x*b x) b σ 1 (-t) (hu.mul hb) hb (fun i => Fin.elim0 i)
  have he : (fun x => 1*(u x*b x)+ -t*b x) = (fun x => (u x-t)*b x) := by funext x;ring
  rw [he,hh] at hl
  linarith

lemma ae_fullSlice_level_eval {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i)) (i : Fin k)
    {b : X → ℝ} (hb : BoundedLip b) (σ : Fin 0 → X → ℝ) :
    ∀ᵐ z : Euc k, fullSlice h π z (fun x => π i x*b x) σ = z i*fullSlice h π z b σ := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    let P (z : Euc (k+1)) := fullSlice h π z (fun x => π i x*b x) σ = z i*fullSlice h π z b σ
    have hm : MeasurableSet {z | P z} := measurableSet_eq_fun
      (measurable_fullSlice h π hπ _ _) (((PiLp.continuous_apply 2 _ i).measurable).mul (measurable_fullSlice h π hπ b σ))
    have hp : ∀ᵐ p : ℝ × Euc k ∂volume.prod volume, P ((Prism.split k).symm p) := by
      apply (Measure.ae_prod_iff_ae_ae (hm.preimage (Prism.split k).symm.continuous.measurable)).mpr
      dsimp only [P,mem_ofPred_eq]
      refine Fin.cases ?_ (fun j => ?_) i
      · filter_upwards [ae_normalSlice_mass_level h hX (hπ 0)] with t ht
        filter_upwards [] with z
        exact level_eval_of_carrier (fullSlice_approx (normalSlice_approx h (π 0) t) (Fin.tail π) z).metric
          (hπ 0) t
          (by simpa only [sub_ne_zero] using (massMeasure_fullSlice_nonzero_zero
            (normalSlice_approx h (π 0) t) (Fin.tail π) (fun j => (hπ j.succ).1.choose_spec.continuous)
            (boundedLip_sub_const (hπ 0) t) (by simpa only [sub_ne_zero] using ht) z)) hb σ
      · exact Eventually.of_forall fun t => ih (normalSlice_approx h (π 0) t)
          (Fin.tail π) (fun j => hπ j.succ) j
    have hh := (Prism.split_measurePreserving k).quasiMeasurePreserving.ae hp
    simpa only [Measure.volume_eq_prod,Function.comp_def,ContinuousLinearEquiv.symm_apply_apply] using hh

lemma ae_fullSlice_mass_level {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i)) (i : Fin k) :
    ∀ᵐ z : Euc k, currentMassMeasure (fullSlice_approx h π z).metric {x | π i x ≠ z i} = 0 := by
  let W (z : Euc k) := weightedCurrent (currentMassMeasure (fullSlice_approx h π z).metric)
    (fullSlice_approx h π z).metric (fun x => π i x-z i)
  have hW z : IsMetricCurrent (W z) :=
    weightedCurrent_boundedLip_isMetricCurrent _ (boundedLip_sub_const (hπ i) (z i))
  have he : ∀ᵐ z : Euc k, W z = (0 : Functional X 0) := by
    apply ae_eq_of_ae_test_eq volume (Eventually.of_forall hW) (Eventually.of_forall fun _ => isMetricCurrent_zero 0)
    intro b σ hab
    filter_upwards [ae_fullSlice_level_eval h hX π hπ i hab.1 σ] with z hz
    change weightedCurrent _ (fullSlice_approx h π z).metric _ b σ = 0
    rw [weightedCurrent_boundedLip_apply (fullSlice_approx h π z).metric (boundedLip_sub_const (hπ i) (z i)) hab]
    have hl := (fullSlice_approx h π z).metric.linearFirst (fun x => π i x*b x) b σ 1 (-(z i))
      ((hπ i).mul hab.1) hab.1 hab.2
    have hw : (fun x => 1*(π i x*b x)+ -(z i)*b x) = (fun x => (π i x-z i)*b x) := by funext x;ring
    rw [hw,hz] at hl
    simpa only [Pi.zero_apply] using hl.trans (by ring)
  filter_upwards [he] with z hz
  have hh : currentMassMeasure (fullSlice_approx h π z).metric {x | π i x-z i ≠ 0} = 0 := by
    apply massMeasure_nonzero_zero_of_mul_zero _ (boundedLip_sub_const (hπ i) (z i))
    intro b σ hab
    rw [←weightedCurrent_boundedLip_apply (fullSlice_approx h π z).metric (boundedLip_sub_const (hπ i) (z i)) hab]
    exact congrFun (congrFun hz b) σ
  simpa only [sub_ne_zero] using hh

abbrev coordinateMap {k : ℕ} (π : Fin k → X → ℝ) (x : X) : Euc k := WithLp.toLp 2 (fun i => π i x)

lemma ae_fullSlice_mass_fiber {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i)) :
    ∀ᵐ z : Euc k, currentMassMeasure (fullSlice_approx h π z).metric {x | coordinateMap π x ≠ z} = 0 := by
  filter_upwards [ae_all_iff.mpr (fun i => ae_fullSlice_mass_level h hX π hπ i)] with z hz
  apply measure_mono_null (t := ⋃ i, {x | π i x ≠ z i}) ?_ (measure_iUnion_null fun i => hz i)
  intro x hx
  apply mem_iUnion.mpr
  by_contra hn
  push Not at hn
  exact hx (by ext i; simpa only [mem_ofPred_eq,not_not] using hn i)

lemma ae_fullSlice_weighted {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i))
    {φ : Euc k → ℝ} (hφπ : BoundedLip (φ ∘ coordinateMap π))
    {b : X → ℝ} (hb : BoundedLip b) (σ : Fin 0 → X → ℝ) :
    ∀ᵐ z : Euc k, fullSlice h π z (fun x => φ (coordinateMap π x)*b x) σ =
      φ z*fullSlice h π z b σ := by
  filter_upwards [ae_fullSlice_mass_fiber h hX π hπ] with z hz
  apply level_eval_of_carrier (fullSlice_approx h π z).metric hφπ (φ z) ?_ hb σ
  apply measure_mono_null (t := {x | coordinateMap π x ≠ z}) ?_ hz
  intro x hx he
  exact hx (congrArg φ he)

lemma fullSlice_weighted_integral {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i))
    {φ : Euc k → ℝ} (hφπ : BoundedLip (φ ∘ coordinateMap π))
    {b : X → ℝ} (hb : BoundedLip b) :
    Integrable (fun z : Euc k => φ z*fullSlice h π z b (fun j => Fin.elim0 j)) ∧
      T (fun x => φ (coordinateMap π x)*b x) π =
        ∫ z : Euc k, φ z*fullSlice h π z b (fun j => Fin.elim0 j) := by
  have he := ae_fullSlice_weighted h hX π hπ hφπ hb (fun j => Fin.elim0 j)
  refine ⟨(fullSlice_eval_integrable h hX π hπ (hφπ.mul hb) _).congr he,?_⟩
  exact (fullSlice_action_integral h hX π hπ (hφπ.mul hb)).trans (integral_congr_ae he)

end CAT0Fillings.Slicing
end

end OAI
