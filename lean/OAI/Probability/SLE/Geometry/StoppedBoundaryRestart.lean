import OAI.Probability.SLE.StoppedMeasures
import OAI.Probability.SLE.LowerPositivity
import OAI.Probability.SLE.Geometry.BoundaryNull
import OAI.Probability.SLE.Geometry.PublishedBoundaryExtension
import OAI.Probability.SLE.Geometry.GeometricTubeSupport

namespace OAI

/-!
The stopped restart identity at every future time. Positive gauge measure on
each nondegenerate trace segment and nullity of the real axis force interior
trace times to be dense. This is a measurable path property, hence transfers
through the actual stopped trace law. Continuity of the published inverse-map
boundary extension then gives the identity also at boundary visits.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.StoppedBoundaryRestart

/-- A positive-mass trace segment cannot lie on the null real axis. -/
theorem segment_has_interior_time
    (γ : ℝ≥0 → ℂ) (μ : Measure ℂ) (hH : ∀ u, 0 ≤ (γ u).im)
    (hnull : μ (range ((↑) : ℝ → ℂ)) = 0)
    {s t : ℝ≥0} (hpos : 0 < μ (γ '' Icc s t)) :
    ∃ u ∈ Icc s t, γ u ∈ upperHalfPlane := by
  by_contra hn
  have hsub : γ '' Icc s t ⊆ range ((↑) : ℝ → ℂ) := by
    rintro z ⟨u, hu, rfl⟩
    have hi : (γ u).im = 0 := le_antisymm
      (le_of_not_gt (fun hp => hn ⟨u, hu, hp⟩)) (hH u)
    refine ⟨(γ u).re, ?_⟩
    apply Complex.ext <;> simp [hi]
  have hz : μ (γ '' Icc s t) = 0 := measure_mono_null hsub hnull
  simp only [hz, lt_self_iff_false] at hpos

/-- Positive mass on every positive-time segment makes the interior trace
visits dense, including at time zero. -/
theorem dense_interior_times
    (γ : ℝ≥0 → ℂ) (μ : Measure ℂ) (hH : ∀ u, 0 ≤ (γ u).im)
    (hnull : μ (range ((↑) : ℝ → ℂ)) = 0)
    (hpos : ∀ s t : ℝ≥0, 0 < s → s < t → 0 < μ (γ '' Icc s t)) :
    Dense {u : ℝ≥0 | γ u ∈ upperHalfPlane} := by
  apply dense_of_exists_between
  intro a b hab
  obtain ⟨s, has, hsb⟩ := exists_between hab
  obtain ⟨t, hst, htb⟩ := exists_between hsb
  obtain ⟨u, hu, hγu⟩ := segment_has_interior_time γ μ hH hnull
    (hpos s t (lt_of_le_of_lt (show (0 : ℝ≥0) ≤ a from bot_le) has) hst)
  exact ⟨u, hγu, has.trans_le hu.1, hu.2.trans_lt htb⟩

local instance : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
local instance : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

/-- Countably many open hit tests encode dense interior trace times. -/
def CountableInteriorHits (p : C(ℝ≥0, ℂ)) : Prop :=
  ∀ i j : ℕ, denseSeq ℝ≥0 i < denseSeq ℝ≥0 j →
    ∃ k : ℕ, denseSeq ℝ≥0 i < denseSeq ℝ≥0 k ∧
      denseSeq ℝ≥0 k < denseSeq ℝ≥0 j ∧ p (denseSeq ℝ≥0 k) ∈ upperHalfPlane

theorem countableInteriorHits_iff (p : C(ℝ≥0, ℂ)) :
    CountableInteriorHits p ↔ Dense {t : ℝ≥0 | p t ∈ upperHalfPlane} := by
  constructor
  · intro hh
    apply dense_of_exists_between
    intro a b hab
    obtain ⟨i, hi⟩ := (denseRange_denseSeq ℝ≥0).exists_mem_open isOpen_Ioo
      (nonempty_Ioo.mpr hab)
    obtain ⟨j, hj⟩ := (denseRange_denseSeq ℝ≥0).exists_mem_open isOpen_Ioo
      (nonempty_Ioo.mpr hi.2)
    obtain ⟨k, hik, hkj, hk⟩ := hh i j hj.1
    exact ⟨denseSeq ℝ≥0 k, hk, hi.1.trans hik, hkj.trans hj.2⟩
  · intro hd i j hij
    obtain ⟨t, htH, ht⟩ := hd.exists_between hij
    obtain ⟨k, hk⟩ := (denseRange_denseSeq ℝ≥0).exists_mem_open
      (isOpen_Ioo.inter (isOpen_upperHalfPlane.preimage p.continuous)) ⟨t, ht, htH⟩
    exact ⟨k, hk.1.1, hk.1.2, hk.2⟩

theorem measurableSet_countableInteriorHits :
    MeasurableSet {p : C(ℝ≥0, ℂ) | CountableInteriorHits p} := by
  simp only [CountableInteriorHits, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases hij : denseSeq ℝ≥0 i < denseSeq ℝ≥0 j
  · simp only [hij, iInter_true, ofPred_exists]
    apply MeasurableSet.iUnion
    intro k
    by_cases hk : denseSeq ℝ≥0 i < denseSeq ℝ≥0 k ∧
        denseSeq ℝ≥0 k < denseSeq ℝ≥0 j
    · simp only [hk.1, hk.2, true_and]
      exact (isOpen_upperHalfPlane.preimage (continuous_eval_const _)).measurableSet
    · have he : {p : C(ℝ≥0, ℂ) | denseSeq ℝ≥0 i < denseSeq ℝ≥0 k ∧
          denseSeq ℝ≥0 k < denseSeq ℝ≥0 j ∧ p (denseSeq ℝ≥0 k) ∈ upperHalfPlane} = ∅ := by
        ext p
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun hp => hk ⟨hp.1, hp.2.1⟩
      rw [he]
      exact MeasurableSet.empty
  · simp only [hij, iInter_false]
    exact MeasurableSet.univ

def GoodBoundaryPath (p : C(ℝ≥0, ℂ)) : Prop :=
  CountableInteriorHits p ∧ ∀ t, 0 ≤ (p t).im

theorem measurableSet_goodBoundaryPath :
    MeasurableSet {p : C(ℝ≥0, ℂ) | GoodBoundaryPath p} := by
  change MeasurableSet ({p : C(ℝ≥0, ℂ) | CountableInteriorHits p} ∩
    {p : C(ℝ≥0, ℂ) | ∀ t, 0 ≤ (p t).im})
  apply measurableSet_countableInteriorHits.inter
  have he : {p : C(ℝ≥0, ℂ) | ∀ t, 0 ≤ (p t).im} =
      ⋂ t : ℝ≥0, {p : C(ℝ≥0, ℂ) | 0 ≤ (p t).im} := by ext p; simp
  rw [he]
  exact (isClosed_iInter (fun t => isClosed_le continuous_const
    (Complex.continuous_im.comp (continuous_eval_const t)))).measurableSet

/-- Only continuity and density are needed to fill in the boundary-time
values of an inverse-chart identity. -/
theorem extend_restart_identity
    (p : C(ℝ≥0, ℂ)) (γ : ℝ≥0 → ℂ) (hγ : Continuous γ)
    (Fbar : ℂ → OnePoint ℂ)
    (hFbar : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
    (hp : GoodBoundaryPath p)
    (heq : ∀ t, p t ∈ upperHalfPlane → (γ t : OnePoint ℂ) = Fbar (p t)) :
    ∀ t, (γ t : OnePoint ℂ) = Fbar (p t) := by
  have hc : Continuous (Fbar ∘ p) := hFbar.comp_continuous p.continuous hp.2
  have hset : IsClosed {t : ℝ≥0 | (γ t : OnePoint ℂ) = Fbar (p t)} :=
    isClosed_eq (OnePoint.continuous_coe.comp hγ) hc
  have hsub : {t : ℝ≥0 | p t ∈ upperHalfPlane} ⊆
      {t : ℝ≥0 | (γ t : OnePoint ℂ) = Fbar (p t)} := fun t ht => heq t ht
  have hall := closure_minimal hsub hset
  rw [(countableInteriorHits_iff p).mp hp.1 |>.closure_eq] at hall
  exact fun t => hall (mem_univ t)

/-- The proved lower Hausdorff estimate and real-axis nullity give the
measurable dense-interior path property for ordinary SLE. -/
theorem ordinarySLE_ae_goodBoundaryPath
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hcont : ∀ ω, Continuous (γ ω))
    (hSLE : IsOrdinaryChordalSLE κ γ P) :
    ∀ᵐ ω ∂P, GoodBoundaryPath (sourceTracePath γ hcont ω) := by
  obtain ⟨_, _, htrace⟩ := hSLE.2
  have hpos := sourceLowerMain_proved Ω inferInstance P inferInstance κ hκ hκ8
    γ hSLE (explicitGauge κ)
    (explicitGauge_isGauge hκ)
    (explicitGauge_small_formula κ)
  have hnull := explicit_gauge_real_axis_null hκ
    (explicitGauge_isGauge hκ)
    (explicitGauge_small_formula κ)
  filter_upwards [hpos, htrace] with ω hp ht
  obtain ⟨G, F, hw⟩ := ht
  refine ⟨(countableInteriorHits_iff _).mpr ?_, hw.2.2.1⟩
  exact dense_interior_times (γ ω) (hausdorffGauge (explicitGauge κ))
    hw.2.2.1 hnull hp

/-- The actual stopped trace law admits the continuous boundary restart
identity at every future time, conditional only on the cited deterministic
Rohde–Schramm boundary-extension input. -/
theorem stopped_boundary_restart
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω))
    (hpublished : PublishedLoewnerBoundaryExtension) :
    ∃ Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ), Measurable Φ ∧
      (∀ ω, Φ (sourceDriverPath B hc ω) = sourceTracePath γ (fun ω => (hw ω).1) ω) ∧
      ∀ (τ : Ω → ℝ≥0)
        (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
          (fun ω => (τ ω : WithTop ℝ≥0))),
        (∀ (A : Set Ω), MeasurableSet[hτ.measurableSpace] A →
          (P.restrict A).map (fun ω => Φ (sourceRestartDriverPath B hc τ ω)) =
            P A • P.map (sourceTracePath γ (fun ω => (hw ω).1))) ∧
        (∀ᵐ ω ∂P, ∃ Fbar : ℂ → OnePoint ℂ,
          ContinuousOn Fbar {z : ℂ | 0 ≤ z.im} ∧
          (∀ z ∈ upperHalfPlane, Fbar z =
            (F ω (τ ω) ((Real.sqrt κ * B (τ ω) ω : ℝ) + z) : OnePoint ℂ)) ∧
          Fbar 0 = (γ ω (τ ω) : OnePoint ℂ) ∧
          ∀ t : ℝ≥0, (γ ω (τ ω + t) : OnePoint ℂ) =
            Fbar (Φ (sourceRestartDriverPath B hc τ ω) t)) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨Φ, hΦm, hΦ, hlaw⟩ := sourceStoppedTraceLaw κ hκ hκ8 B hB hm hc γ G F hw
  let gp := sourceTracePath γ (fun ω => (hw ω).1)
  have hgm : Measurable gp := by
    have he : gp = fun ω => Φ (sourceDriverPath B hc ω) := funext fun ω => (hΦ ω).symm
    rw [he]
    exact hΦm.comp (source_path_measurable (sourceDriverPath B hc) hm)
  have hSLE : IsOrdinaryChordalSLE κ γ P := by
    refine ⟨fun t => (continuous_eval_const t).measurable.comp hgm, B, hB, ?_⟩
    exact Eventually.of_forall (fun ω => ⟨G ω, F ω, hw ω⟩)
  have hgood : ∀ᵐ ω ∂P, GoodBoundaryPath (gp ω) :=
    ordinarySLE_ae_goodBoundaryPath hκ hκ8 γ (fun ω => (hw ω).1) hSLE
  have hgoodLaw : ∀ᵐ p ∂P.map gp, GoodBoundaryPath p :=
    (ae_map_iff hgm.aemeasurable measurableSet_goodBoundaryPath).mpr hgood
  refine ⟨Φ, hΦm, hΦ, ?_⟩
  intro τ hτ
  refine ⟨(hlaw τ hτ).1, ?_⟩
  let rp := sourceRestartDriverPath B hc τ
  have hrm : Measurable rp := source_path_measurable rp (fun t =>
    (measurable_pi_apply t).comp (brownianRestart_measurable hm hc
      (stopping_time_measurable_nnreal hτ)))
  have hrestartLaw : P.map (fun ω => Φ (rp ω)) = P.map gp := by
    simpa only [Measure.restrict_univ, measure_univ, one_smul] using
      (hlaw τ hτ).1 univ MeasurableSet.univ
  have hgoodRestart : ∀ᵐ ω ∂P, GoodBoundaryPath (Φ (rp ω)) := by
    have he := hgoodLaw
    rw [← hrestartLaw] at he
    exact (ae_map_iff (hΦm.comp hrm).aemeasurable measurableSet_goodBoundaryPath).mp he
  filter_upwards [hgoodRestart, (hlaw τ hτ).2] with ω hgoodω heq
  obtain ⟨Fbar, hFc, hFH, hF0⟩ := normalized_capacity_inverse_boundary_extension
    hpublished (continuous_const.mul (hc ω)) (hw ω) (τ ω) 1 zero_lt_one
  have hFH' : ∀ z ∈ upperHalfPlane, Fbar z =
      (F ω (τ ω) ((Real.sqrt κ * B (τ ω) ω : ℝ) + z) : OnePoint ℂ) := by
    simpa only [Complex.ofReal_one, one_mul, Pi.mul_apply] using hFH
  refine ⟨Fbar, hFc, hFH', hF0, ?_⟩
  apply extend_restart_identity (Φ (rp ω)) (fun t => γ ω (τ ω + t))
    ((hw ω).1.comp (continuous_const.add continuous_id)) Fbar hFc hgoodω
  intro t ht
  rw [hFH' _ ht, heq t ht, add_comm (Φ (rp ω) t)]

/-- A tube event maps back to the physical domain at every time, including
boundary visits, under the continuous boundary restart identity. -/
theorem boundary_restart_tube_transfer
    (p : C(ℝ≥0, ℂ)) (γ : ℝ≥0 → ℂ) (τ : ℝ≥0) (Fbar : ℂ → OnePoint ℂ)
    (heq : ∀ t, (γ (τ + t) : OnePoint ℂ) = Fbar (p t))
    (N V O W : Set ℂ)
    (hN : MapsTo Fbar N (((↑) : ℂ → OnePoint ℂ) '' O))
    (hV : MapsTo Fbar V (((↑) : ℂ → OnePoint ℂ) '' W))
    (hp : p ∈ pathTubeEvent N V) :
    ∃ T : ℝ≥0, 0 < T ∧ MapsTo (fun t => γ (τ + t)) (Icc 0 T) O ∧ γ (τ + T) ∈ W := by
  obtain ⟨T, hT, hpN, hpV⟩ := hp
  have hmap {A S : Set ℂ} (hh : MapsTo Fbar A (((↑) : ℂ → OnePoint ℂ) '' S))
      (t : ℝ≥0) (ht : p t ∈ A) : γ (τ + t) ∈ S := by
    obtain ⟨z, hz, he⟩ := hh ht
    have hz' : z = γ (τ + t) := OnePoint.coe_injective (he.trans (heq t).symm)
    exact hz' ▸ hz
  exact ⟨T, hT, fun t ht => hmap hN t (hpN ht), hmap hV T hpV⟩

/-- A past-restricted stopped-law tube probability is a lower bound for
any physical event containing that tube almost surely. This formulation
uses the full-measure boundary restart identity without imposing pathwise
identities on exceptional samples. -/
theorem restricted_tube_probability_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : Ω → C(ℝ≥0, ℂ)) (hp : Measurable p) (Q : Measure C(ℝ≥0, ℂ))
    (A C : Set Ω) (hC : MeasurableSet C) (N V : Set ℂ)
    (hN : IsOpen N) (hV : IsOpen V)
    (hlaw : (P.restrict A).map p = P A • Q)
    (htransfer : ∀ᵐ ω ∂P, p ω ∈ pathTubeEvent N V → ω ∈ C) :
    P A * Q (pathTubeEvent N V) ≤ P (A ∩ C) := by
  have ht := measurableSet_pathTubeEvent hN hV
  calc
    P A * Q (pathTubeEvent N V) = (P.restrict A).map p (pathTubeEvent N V) := by
      rw [hlaw, Measure.smul_apply, smul_eq_mul]
    _ = (P.restrict A) (p ⁻¹' pathTubeEvent N V) := Measure.map_apply hp ht
    _ ≤ (P.restrict A) C := measure_mono_ae (ae_restrict_of_ae htransfer)
    _ = P (A ∩ C) := by rw [Measure.restrict_apply hC, inter_comm]

end SLEExactGauge.StoppedBoundaryRestart

end

end OAI
