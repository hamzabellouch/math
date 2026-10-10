import Mathlib
import OAI.Geometry.CAT0Fillings.Slicing.Iterated
import OAI.Geometry.CAT0Fillings.Slices.WeakApproximation

namespace OAI

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelRestriction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma NormalApprox.normal {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) :
    IsMetricCurrent T ∧ IsMetricCurrent (boundarySucc T) := by
  obtain ⟨C,Ts,hTs,hM,hN,hlim⟩ := h
  cases k with
  | zero =>
    obtain ⟨hT,hB⟩ := normal_one_of_bounded_integral_weak_limit hTs C C hM hN hlim
    exact ⟨hT,hB.1⟩
  | succ k => exact normal_of_bounded_integral_weak_limit hTs C C hM hN hlim

lemma NormalApprox.integral_zero {T : Functional X 0} (h : NormalApprox 0 T) :
    IsIntegral 0 T := by
  obtain ⟨C,Ts,hTs,hM,_,hlim⟩ := h
  exact integral_zero_weak_closed hTs C hM hlim

lemma NormalApprox.slice_tree {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X) : IntegralSliceTree k T := by
  obtain ⟨C,Ts,hTs,hM,hN,hlim⟩ := h
  exact integral_slice_tree_of_bounded_weak_limit hTs C C hM hN hlim hX

theorem NormalApprox.ae_slice {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∀ᵐ t : ℝ, NormalApprox k (superlevelSlice hT hB u t) := by
  obtain ⟨C,Ts,hTs,hM,hN,hlim⟩ := h
  have hu : BoundedLip u := boundedLip_of_lipschitz hK
  obtain ⟨ψ,hψ,μs,νs,μ,ν,hμs,hμ,hνs,hν,hμlim,hνlim⟩ :=
    exists_joint_weak_controlling_subsequence (fun j => (hTs j).1)
      (fun j => (hTs j).2.2.1) C C hM hN hlim (boundarySucc_weak_limit hlim)
  have hweak := ae_superlevelSlice_weak_tendsto (fun j => (hTs (ψ j)).1) hT
    (fun j => (hTs (ψ j)).2.2.1) hB μs νs μ ν hμs hμ hνs hν hμlim hνlim
    (fun b π => (hlim b π).comp hψ.tendsto_atTop) hu
  cases k with
  | zero =>
    choose G hG hG0 hGI hS using fun j => superlevelSlice_coarea_bound (hTs (ψ j)) hX hK
    have hGI' j : (∫ t : ℝ, G j t) ≤ (K : ℝ)*C :=
      (hGI j).trans (mul_le_mul_of_nonneg_left (hM (ψ j)) K.coe_nonneg)
    have hfat := ae_exists_bounded_subsequence_of_integral_bound volume hG
      (fun j => Eventually.of_forall (hG0 j)) ((K : ℝ)*C) hGI'
    filter_upwards [hweak,ae_all_iff.mpr hS,hfat] with t ht hs hf
    obtain ⟨D,χ,hχ,hD⟩ := hf
    let R : ℝ≥0 := ⟨max D 0,le_max_right _ _⟩
    let Ss : ℕ → Functional X 0 := fun j =>
      superlevelSlice (hTs (ψ (χ j))).1 (hTs (ψ (χ j))).2.2.1 u t
    have hSs j : IsIntegral 0 (Ss j) := ⟨(hs (χ j)).1,(hs (χ j)).2.1⟩
    apply normalApprox_of_weak_limit hSs R 0
    · intro j
      exact ((hs (χ j)).2.2.trans (hD j)).trans (le_max_left _ _)
    · intro j
      simp only [boundary,mass_zero,NNReal.coe_zero,le_refl]
    · intro b π
      exact (ht b π).comp hχ.tendsto_atTop
  | succ k =>
    choose G H hG hH hG0 hH0 hGI hHI hS using fun j =>
      superlevelSlice_normal_coarea_bound (hTs (ψ j)) hX hK
    have hsum j : Integrable (fun t => G j t + H j t) volume := (hG j).add (hH j)
    have hsum0 j : 0 ≤ᵐ[volume] (fun t => G j t + H j t) :=
      Eventually.of_forall fun t => add_nonneg (hG0 j t) (hH0 j t)
    have hsumI j : (∫ t : ℝ, G j t + H j t) ≤ (K : ℝ)*(C+C) := by
      rw [integral_add (hG j) (hH j),mul_add]
      exact add_le_add ((hGI j).trans (mul_le_mul_of_nonneg_left (hM (ψ j)) K.coe_nonneg))
        ((hHI j).trans (mul_le_mul_of_nonneg_left (hN (ψ j)) K.coe_nonneg))
    have hfat := ae_exists_bounded_subsequence_of_integral_bound volume hsum hsum0
      ((K : ℝ)*(C+C)) hsumI
    filter_upwards [hweak,ae_all_iff.mpr hS,hfat] with t ht hs hf
    obtain ⟨D,χ,hχ,hD⟩ := hf
    let R : ℝ≥0 := ⟨max D 0,le_max_right _ _⟩
    let Ss : ℕ → Functional X (k+1) := fun j =>
      superlevelSlice (hTs (ψ (χ j))).1 (hTs (ψ (χ j))).2.2.1 u t
    have hSs j : IsIntegral (k+1) (Ss j) := (hs (χ j)).1
    apply normalApprox_of_weak_limit hSs R R
    · intro j
      exact (((hs (χ j)).2.1.trans (le_add_of_nonneg_right (hH0 (χ j) t))).trans
        (hD j)).trans (le_max_left _ _)
    · intro j
      exact (((hs (χ j)).2.2.trans (le_add_of_nonneg_left (hG0 (χ j) t))).trans
        (hD j)).trans (le_max_left _ _)
    · intro b π
      exact (ht b π).comp hχ.tendsto_atTop

omit [Nonempty X] in
lemma superlevelSlice_offDomain [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    (u : X → ℝ) (t : ℝ) (b : X → ℝ) (π : Fin k → X → ℝ)
    (hab : ¬Admissible b π) : superlevelSlice hT hB u t b π = 0 := by
  simp only [superlevelSlice,Pi.sub_apply,restrictCurrent,boundarySucc,ite_eq_right hab,sub_zero]

omit [Nonempty X] in
lemma superlevelSlice_testClass_continuous [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} (hu : Continuous u) (t : ℝ) (K : ℕ) :
    Continuous (TestClass.eval (K := K) (superlevelSlice hT hB u t)) := by
  have hE : MeasurableSet {x | t < u x} := measurableSet_lt measurable_const hu.measurable
  have hR := Foundations.IsMetricCurrent.testClass_continuous
    (restrictCurrent_isMetricCurrent hB hE) K
  have hQ := Foundations.IsMetricCurrent.boundary_testClass_continuous
    (restrictCurrent_isMetricCurrent hT hE) K
  convert hR.sub hQ using 1
  rfl

theorem measurableSet_slice_normalApprox {A : Type*} [MeasurableSpace A] {k : ℕ}
    (T : A → Functional X (k+1))
    (hT : ∀ a, IsMetricCurrent (T a)) (hB : ∀ a, IsMetricCurrent (boundarySucc (T a)))
    (hTm : ∀ b π, Measurable (fun a => T a b π))
    {u : X → ℝ} (hu : BoundedLip u) :
    MeasurableSet {p : ℝ × A | NormalApprox k (superlevelSlice (hT p.2) (hB p.2) u p.1)} := by
  apply measurableSet_normalApprox
  · intro p
    exact superlevelSlice_offDomain (hT p.2) (hB p.2) u p.1
  · intro p K
    exact superlevelSlice_testClass_continuous (hT p.2) (hB p.2) hu.continuous p.1 K
  · exact measurable_superlevelSlice_family T hT hB hTm hu

lemma NormalApprox.current {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) : IsMetricCurrent T := by
  cases k with
  | zero => exact h.integral_zero.1
  | succ k => exact h.normal.1

omit [Nonempty X] in
lemma normalApprox_of_integral [Nonempty X] {k : ℕ} {T : Functional X k}
    (hT : IsIntegral k T) : NormalApprox k T := by
  have hM : 0 ≤ mass T := mass_nonneg T
  have hN : 0 ≤ mass (boundary T) := mass_nonneg _
  exact normalApprox_of_weak_limit (fun _ => hT) ⟨mass T,hM⟩ ⟨mass (boundary T),hN⟩
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ _ => tendsto_const_nhds)

lemma normalApprox_zero (k : ℕ) : NormalApprox k (0 : Functional X k) :=
  normalApprox_of_integral (isIntegral_zero k)

noncomputable def normalSlice {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (u : X → ℝ) (t : ℝ) : Functional X k := by
  classical
  exact if NormalApprox k (superlevelSlice h.normal.1 h.normal.2 u t)
  then superlevelSlice h.normal.1 h.normal.2 u t else 0

lemma normalSlice_approx {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (u : X → ℝ) (t : ℝ) :
    NormalApprox k (normalSlice h u t) := by
  classical
  unfold normalSlice
  split_ifs with hh
  · exact hh
  · exact normalApprox_zero k

lemma ae_normalSlice_eq {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    normalSlice h u =ᵐ[volume] superlevelSlice h.normal.1 h.normal.2 u := by
  filter_upwards [h.ae_slice hX h.normal.1 h.normal.2 hK] with t ht
  classical
  exact ite_eq_left ht

lemma measurable_normalSlice_family {A : Type*} [MeasurableSpace A] {k : ℕ}
    (T : A → Functional X (k+1)) (h : ∀ a, NormalApprox (k+1) (T a))
    (hTm : ∀ b π, Measurable (fun a => T a b π))
    {u : X → ℝ} (hu : BoundedLip u) (b : X → ℝ) (π : Fin k → X → ℝ) :
    Measurable (fun p : ℝ × A => normalSlice (h p.2) u p.1 b π) := by
  classical
  have hE := measurableSet_slice_normalApprox T (fun a => (h a).normal.1)
    (fun a => (h a).normal.2) hTm hu
  have hS := measurable_superlevelSlice_family T (fun a => (h a).normal.1)
    (fun a => (h a).normal.2) hTm hu b π
  simpa only [normalSlice,ite_apply,Pi.zero_apply] using
    (Measurable.ite hE hS (measurable_const (a := (0:ℝ))))

end CAT0Fillings.Slicing
end

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

def NormalApproxAt (k C : ℕ) (T : Functional X k) : Prop :=
  ∃ Ts : ℕ → Functional X k, (∀ j, IsIntegral k (Ts j)) ∧
    (∀ j, mass (Ts j) ≤ C) ∧ (∀ j, mass (boundary (Ts j)) ≤ C) ∧
    ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π))

omit [Nonempty X] in
lemma normalApproxAt_iff_closed [Nonempty X] {k C : ℕ} {T : Functional X k}
    (hOff : ∀ b π, ¬Admissible b π → T b π = 0)
    (hCont : ∀ K, Continuous (TestClass.eval (K := K) T)) :
    NormalApproxAt k C T ↔ currentCoordinates k T ∈ normalApproxClosed (X := X) k C := by
  classical
  constructor
  · rintro ⟨Ts,hTs,hM,hN,hlim⟩
    apply isClosed_closure.mem_of_tendsto (tendsto_pi_nhds.mpr fun ij => hlim _ _)
    exact Eventually.of_forall fun j => subset_closure ⟨Ts j,⟨hTs j,hM j,hN j⟩,rfl⟩
  · intro hC
    obtain ⟨ys,hys,hlim⟩ := mem_closure_iff_seq_limit.mp hC
    choose Ts hTs heq using hys
    refine ⟨Ts,fun j => (hTs j).1,fun j => (hTs j).2.1,fun j => (hTs j).2.2,?_⟩
    apply weak_limit_of_coordinate_limit (fun j => (hTs j).1) C C
      (fun j => (hTs j).2.1) (fun j => (hTs j).2.2) hOff hCont
    simpa only [heq] using hlim

lemma measurableSet_normalApproxAt {A : Type*} [MeasurableSpace A] {k C : ℕ}
    (T : A → Functional X k) (h : ∀ a, IsMetricCurrent (T a))
    (hm : ∀ b π, Measurable (fun a => T a b π)) :
    MeasurableSet {a | NormalApproxAt k C (T a)} := by
  have he : {a | NormalApproxAt k C (T a)} =
      (fun a => currentCoordinates k (T a)) ⁻¹' normalApproxClosed (X := X) k C := by
    ext a
    exact normalApproxAt_iff_closed (h a).offDomain
      (fun K => Foundations.IsMetricCurrent.testClass_continuous (h a) K)
  rw [he]
  exact isClosed_closure.measurableSet.preimage (Measurable.of_eval fun ij => hm _ _)

noncomputable def NormalApprox.cost {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) : ℕ := by
  classical
  exact Nat.find h

omit [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma NormalApprox.cost_spec [BorelSpace X] [CompactSpace X] [Nonempty X]
    {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) : NormalApproxAt k h.cost T := by
  classical
  exact Nat.find_spec h

omit [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma NormalApprox.cost_le [BorelSpace X] [CompactSpace X] [Nonempty X]
    {k C : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hC : NormalApproxAt k C T) : h.cost ≤ C := by
  classical
  exact Nat.find_min' h hC

lemma measurable_normalApprox_cost {A : Type*} [MeasurableSpace A] {k : ℕ}
    (T : A → Functional X k) (h : ∀ a, NormalApprox k (T a))
    (hm : ∀ b π, Measurable (fun a => T a b π)) :
    Measurable (fun a => (h a).cost) := by
  classical
  exact measurable_find h (fun C => measurableSet_normalApproxAt T (fun a => (h a).current) hm)

lemma NormalApprox.mass_le_cost {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) : mass T ≤ h.cost := by
  obtain ⟨Ts,hTs,hM,hN,hlim⟩ := h.cost_spec
  have hcur j : IsMetricCurrent (Ts j) := by cases k <;> exact (hTs j).1
  exact mass_le_of_bounded_weak_limit (h.cost : ℝ≥0) hcur hM (fun b π _ => hlim b π)

omit [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma normalApproxAt_zero [BorelSpace X] [CompactSpace X] [Nonempty X]
    (k C : ℕ) : NormalApproxAt k C (0 : Functional X k) := by
  refine ⟨fun _ => 0,fun _ => isIntegral_zero k,?_,?_,fun _ _ => tendsto_const_nhds⟩
  · intro j
    change mass (fun (_ : X → ℝ) (_ : Fin k → X → ℝ) => 0) ≤ (C:ℝ)
    rw [mass_zero]
    positivity
  · intro j
    change mass (boundary (0 : Functional X k)) ≤ (C:ℝ)
    cases k with
    | zero => change mass (fun (_ : X → ℝ) (_ : Fin 0 → X → ℝ) => 0) ≤ (C:ℝ); rw [mass_zero]; positivity
    | succ k => change mass (boundarySucc (fun (_ : X → ℝ) (_ : Fin (k+1) → X → ℝ) => 0)) ≤ (C:ℝ)
                rw [boundarySucc_zero,mass_zero]
                positivity

lemma NormalApprox.cost_zero {k : ℕ} (h : NormalApprox k (0 : Functional X k)) :
    h.cost = 0 := Nat.eq_zero_of_le_zero (h.cost_le (normalApproxAt_zero k 0))

lemma exists_integrable_subsequence_bound {A : Type*} [MeasurableSpace A]
    (μ : Measure A) {G : ℕ → A → ℝ} (hG : ∀ j, Integrable (G j) μ)
    (hG0 : ∀ j, ∀ᵐ x ∂μ, 0 ≤ G j x) (M : ℝ) (hM : ∀ j, (∫ x, G j x ∂μ) ≤ M) :
    ∃ g : A → ℝ, Integrable g μ ∧ (∀ x, 0 ≤ g x) ∧
      (∫ x, g x ∂μ) ≤ max M 0 ∧
      ∀ᵐ x ∂μ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ j, G (ψ j) x < g x + 1 := by
  let hm (j : ℕ) := (hG j).aemeasurable.ennreal_ofReal
  let f (j : ℕ) : A → ℝ≥0∞ := (hm j).mk _
  have hf (j : ℕ) : Measurable (f j) := (hm j).measurable_mk
  have heq (j : ℕ) : (fun x => ENNReal.ofReal (G j x)) =ᵐ[μ] f j := (hm j).ae_eq_mk
  let H : A → ℝ≥0∞ := fun x => liminf (fun j => f j x) atTop
  have hHm : Measurable H := Measurable.liminf hf
  have hI (j : ℕ) : (∫⁻ x, f j x ∂μ) ≤ ENNReal.ofReal M := by
    rw [←lintegral_congr_ae (heq j),←ofReal_integral_eq_lintegral_ofReal (hG j) (hG0 j)]
    exact ENNReal.ofReal_le_ofReal (hM j)
  have hHI : (∫⁻ x, H x ∂μ) ≤ ENNReal.ofReal M :=
    (lintegral_liminf_le hf).trans (liminf_le_of_frequently_le (Frequently.of_forall hI))
  have hHfin : (∫⁻ x, H x ∂μ) ≠ ⊤ := (hHI.trans_lt ENNReal.ofReal_lt_top).ne
  have hafin := ae_lt_top hHm hHfin
  refine ⟨fun x => (H x).toReal, integrable_toReal_of_lintegral_ne_top hHm.aemeasurable hHfin,
    fun x => ENNReal.toReal_nonneg, ?_, ?_⟩
  · rw [integral_toReal hHm.aemeasurable hafin]
    simpa only [ENNReal.toReal_ofReal'] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hHI
  · filter_upwards [hafin,ae_all_iff.mpr heq] with x hx he
    have hl : H x < ENNReal.ofReal ((H x).toReal + 1) :=
      (ENNReal.lt_ofReal_iff_toReal_lt hx.ne).mpr (by linarith)
    obtain ⟨ψ,hψ,hψb⟩ := extraction_of_frequently_atTop
      (frequently_lt_of_liminf_lt (u := fun j => f j x) (f := atTop) (h := hl))
    refine ⟨ψ,hψ,fun j => ?_⟩
    have hh : ENNReal.ofReal (G (ψ j) x) < ENNReal.ofReal ((H x).toReal + 1) := by
      rw [he]
      exact hψb j
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hh

end CAT0Fillings.Slicing
end

end OAI
