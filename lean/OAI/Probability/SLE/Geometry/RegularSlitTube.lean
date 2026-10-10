import OAI.Probability.SLE.Loewner.RealCharacteristicAvoidance
import OAI.Probability.SLE.Loewner.LoewnerTipVisit
import OAI.Probability.SLE.Geometry.ActualCompactAvoidance

namespace OAI

/-! Open-tube support for a deterministic slit with regular real
characteristics. The slit geometry and the existence of these
characteristics remain explicit deterministic obligations. -/
noncomputable section
open Set Filter Metric _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

def RegularRealCharacteristics (V : ℝ≥0 → ℝ) (T : ℝ≥0) : Prop :=
  ∀ x : ℝ, x ≠ 0 → ∃ q : ℝ → ℝ, q 0=x ∧
    (∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt q
      (2/(q t-V t.toNNReal)) (Icc 0 (T : ℝ)) t) ∧
    ∀ t ∈ Icc 0 (T : ℝ), q t-V t.toNNReal ≠ 0

lemma regular_slit_driver_trace_containment
    {V : ℝ≥0 → ℝ} (hV : Continuous V)
    {β : ℝ≥0 → ℂ} {H J : ℝ≥0 → ℂ → ℂ}
    (hv : IsCapacityTwoWitness V β H J) (T : ℝ≥0)
    (hfree : upperHalfPlane \ (β '' Icc 0 T) ⊆ survivingDomain β T)
    (hreal : RegularRealCharacteristics V T)
    (N : Set ℂ) (hN : IsOpen N) (hsub : β '' Icc 0 T ⊆ N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (U : ℝ≥0 → ℝ), Continuous U →
      ∀ (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ), IsCapacityTwoWitness U γ G F →
      (∀ t ∈ Icc 0 T, |U t-V t| ≤ δ) → MapsTo γ (Icc 0 T) N := by
  apply driver_neighborhood_trace_containment V hV T N hN
  intro z hz hzN
  have hztrace : z ∉ β '' Icc 0 T := fun h => hzN (hsub h)
  by_cases him : 0 < z.im
  · exact stableTraceAvoidance_of_surviving hv T (hfree ⟨him,hztrace⟩)
  · have hz0 : z.im=0 := le_antisymm (le_of_not_gt him) hz
    have hez : z=(z.re : ℂ) := by apply Complex.ext <;> simp [hz0]
    have hx : z.re ≠ 0 := by
      intro he
      have he0 : z=0 := by simpa only [he,Complex.ofReal_zero] using hez
      apply hztrace
      exact ⟨0,⟨le_rfl,zero_le⟩,hv.2.1.trans he0.symm⟩
    obtain ⟨q,hq0,hqd,hn⟩ := hreal z.re hx
    have hh := stableTraceAvoidance_of_real_characteristic V hV T q hqd hn
    rwa [hq0,← hez] at hh

theorem regular_slit_driver_tube
    {V : ℝ≥0 → ℝ} (hV : Continuous V)
    {β : ℝ≥0 → ℂ} {H J : ℝ≥0 → ℂ → ℂ}
    (hv : IsCapacityTwoWitness V β H J) (T : ℝ≥0)
    (hfree : upperHalfPlane \ (β '' Icc 0 T) ⊆ survivingDomain β T)
    (hreal : RegularRealCharacteristics V T) (htip : 0 < (β T).im)
    (N W : Set ℂ) (hN : IsOpen N) (hW : IsOpen W)
    (hsub : β '' Icc 0 T ⊆ N) (hend : β T ∈ W) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (U : ℝ≥0 → ℝ), Continuous U →
      ∀ (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ), IsCapacityTwoWitness U γ G F →
      (∀ t ∈ Icc 0 T, |U t-V t| ≤ δ) →
      ∃ t : ℝ≥0, 0 < t ∧ MapsTo γ (Icc 0 t) N ∧ γ t ∈ W := by
  obtain ⟨δ₁,hδ₁,hstay⟩ := regular_slit_driver_trace_containment hV hv T hfree hreal N hN hsub
  obtain ⟨r,hr,hrW⟩ := Metric.isOpen_iff.mp hW _ hend
  obtain ⟨δ₂,hδ₂,hvisit⟩ := driver_neighborhood_visits_tip hv T (lt_min hr htip)
    (min_le_right r (β T).im) isCompact_empty (empty_subset _)
  refine ⟨min δ₁ δ₂,lt_min hδ₁ hδ₂,?_⟩
  intro U hU γ G F hw hc
  have hs := hstay U hU γ G F hw (fun t ht => (hc t ht).trans (min_le_left _ _))
  obtain ⟨_,t,ht,hb⟩ := hvisit U γ G F hw (fun t ht => (hc t ht).trans (min_le_right _ _))
  have ht0 : 0 < t := by
    by_contra hn
    have he : t=0 := le_antisymm (le_of_not_gt hn) zero_le
    have hi := ball_subset_halfPlane (min_le_right r (β T).im) hb
    rw [he,hw.2.1] at hi
    exact (lt_irrefl (0 : ℝ)) hi
  exact ⟨t,ht0,fun s hs' => hs ⟨hs'.1,hs'.2.trans ht.2⟩,
    hrW ((ball_subset_ball (min_le_left _ _)) hb)⟩

theorem regular_slit_tube_positive
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (V : C(ℝ≥0,ℝ)) (hV0 : V 0=0)
    {β : ℝ≥0 → ℂ} {H J : ℝ≥0 → ℂ → ℂ}
    (hv : IsCapacityTwoWitness V β H J) (T : ℝ≥0) (hT : 0 < T)
    (hfree : upperHalfPlane \ (β '' Icc 0 T) ⊆ survivingDomain β T)
    (hreal : RegularRealCharacteristics V T) (htip : 0 < (β T).im)
    (N W : Set ℂ) (hN : IsOpen N) (hW : IsOpen W)
    (hsub : β '' Icc 0 T ⊆ N) (hend : β T ∈ W) :
    0 < (P.comap (Subtype.val : a.samples → Ω))
      {ω | ∃ t : ℝ≥0, 0 < t ∧ MapsTo (γ ω) (Icc 0 t) N ∧ γ ω t ∈ W} := by
  obtain ⟨δ,hδ,hh⟩ := regular_slit_driver_tube V.continuous hv T hfree hreal htip
    N W hN hW hsub hend
  have hp := regular_scaled_driver_tube_positive a hκ V hV0 T hT hδ
  apply hp.trans_le (measure_mono ?_)
  intro ω hω
  exact hh (fun t => Real.sqrt κ*a.B t ω) (continuous_const.mul (a.continuous_B ω))
    (γ ω) (a.G ω) (a.F ω) (a.witness ω) (fun t ht => (hω t ht).le)

theorem ordinary_regular_slit_tube_positive
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (γ : Ω → ℝ≥0 → ℂ)
    (hSLE : IsOrdinaryChordalSLE κ γ P)
    (V : C(ℝ≥0,ℝ)) (hV0 : V 0=0)
    {β : ℝ≥0 → ℂ} {H J : ℝ≥0 → ℂ → ℂ}
    (hv : IsCapacityTwoWitness V β H J) (T : ℝ≥0) (hT : 0 < T)
    (hfree : upperHalfPlane \ (β '' Icc 0 T) ⊆ survivingDomain β T)
    (hreal : RegularRealCharacteristics V T) (htip : 0 < (β T).im)
    (N W : Set ℂ) (hN : IsOpen N) (hW : IsOpen W)
    (hsub : β '' Icc 0 T ⊆ N) (hend : β T ∈ W) :
    0 < P {ω | ∃ t : ℝ≥0, 0 < t ∧ MapsTo (γ ω) (Icc 0 t) N ∧ γ ω t ∈ W} := by
  obtain ⟨a⟩ := exists_regular_sle_presentation hSLE
  have hp := regular_slit_tube_positive a hκ V hV0 hv T hT hfree hreal htip N W hN hW hsub hend
  apply hp.trans_le
  have hh := Measure.le_map_apply (μ := P.comap (Subtype.val : a.samples → Ω))
    a.measurePreserving_val.measurable.aemeasurable
    {ω | ∃ t : ℝ≥0, 0 < t ∧ MapsTo (γ ω) (Icc 0 t) N ∧ γ ω t ∈ W}
  rw [a.measurePreserving_val.map_eq] at hh
  convert! hh using 1

end SLEExactGauge

end

end OAI
