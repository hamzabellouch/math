import OAI.Probability.SLE.Gauge.StrictPastTilted
import OAI.Probability.SLE.Gauge.ActualPastThreshold

namespace OAI

/-! Passing finite centered-law test bounds to countable detected mass. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
attribute [local instance] Classical.propDecidable

namespace SLEExactGauge.Multipoint

lemma range_image_event_union {X : Type*} (q : ℕ → ℝ≥0) (A : ℝ≥0 → Set X) :
    (⋃ n, ⋃ t∈(Finset.range n).image q, A t) = ⋃ n, A (q n) := by
  ext x
  constructor
  · intro hx
    obtain ⟨n,hx⟩ := mem_iUnion.mp hx
    obtain ⟨t,ht,hxt⟩ := mem_iUnion₂.mp hx
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp ht
    exact mem_iUnion.mpr ⟨k,hxt⟩
  · intro hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n+1,mem_iUnion₂.mpr ⟨q n,
      Finset.mem_image.mpr ⟨n,Finset.mem_range.mpr (Nat.lt_succ_self n),rfl⟩,hn⟩⟩

namespace CanonicalMass

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G) (hB : IsBrownianReal B P)
  (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω = 0)
  (hκ : 0 < κ) (hκ8 : κ < 8) (F : Ω → ℝ≥0 → ℂ → ℂ)
  (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))

include C hB hc h0 hκ hκ8 F hw

lemma countable_strict_past_le_of_finite_bound
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (hmono : Monotone u)
    (hlim : Tendsto u atTop atTop) (J : ℕ → Finset ℝ≥0) (hJ : Monotone J)
    (E : ℝ≥0 → Set Ω)
    (hE : ∀ t, MeasurableSet[(Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) t] (E t))
    (K : Set upperHalfPlane) (hK : IsCompact K) (A : ℝ≥0∞)
    (hbound : ∀ j, ∀ᶠ n in atTop,
      (∫⁻ z in (Subtype.val : upperHalfPlane → ℂ) '' K,
        ENNReal.ofReal (initialGreen κ z) * finiteCenteredLaw P κ B γ G z (u n)
          (finiteStrictPastEvent (J j) E (fun ω => radiusLevelTime (γ ω) (G ω) z (u n))) ∂volume) ≤ A) :
    (∫⁻ ω, C.rational.terminal ω (K ∩ ⋃ n, ⋃ t∈J n,
      if ω∈E t then {z : upperHalfPlane | (z:ℂ)∈γ ω '' Icc 0 t}ᶜ else ∅) ∂P) ≤ A := by
  rw [C.countable_strict_past_expectation hB hc h0 hκ hκ8 F hw J hJ E hE K hK]
  apply iSup_le
  intro j
  rw [← C.finite_strict_past_expectation hB hc h0 hκ hκ8 F hw (J j) E
    (fun t _ => hE t) K hK]
  exact le_of_tendsto (C.finite_strict_past_tilted_limit hB hBm hc h0 hκ hκ8 γ G F hw u hu hmono hlim
    (J j) E (fun t _ => hE t) K hK) (hbound j)

lemma bad_cell_mass_le_of_finite_bound
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (hmono : Monotone u)
    (hlim : Tendsto u atTop atTop) (q : ℕ → ℝ≥0) (hq : DenseRange q)
    (K : Set upperHalfPlane) (hK : IsCompact K) (H : ℝ) (hH : 0 < H) (A : ℝ≥0∞)
    (hbound : ∀ j, ∀ᶠ n in atTop,
      (∫⁻ z in (Subtype.val : upperHalfPlane → ℂ) '' K,
        ENNReal.ofReal (initialGreen κ z) * finiteCenteredLaw P κ B γ G z (u n)
          (finiteStrictPastEvent ((Finset.range j).image q)
            (fun t => {ω | H < (C.process t ω K).toReal})
            (fun ω => radiusLevelTime (γ ω) (G ω) z (u n))) ∂volume) ≤ A) :
    (∫⁻ ω, {ω | ENNReal.ofReal (2*H) < C.rational.terminal ω K}.indicator
      (fun ω => C.rational.terminal ω K) ω ∂P) ≤ 2*A := by
  have hE (t : ℝ≥0) : MeasurableSet[(Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) t]
      {ω | H < (C.process t ω K).toReal} :=
    measurableSet_lt measurable_const
      (((Measure.measurable_coe hK.measurableSet).comp (C.progressive.adapted t)).ennreal_toReal)
  let E (t : ℝ≥0) : Set Ω := {ω | H < (C.process t ω K).toReal}
  let J (n : ℕ) := (Finset.range n).image q
  let D (ω : Ω) := C.rational.terminal ω (K ∩ ⋃ n,
    if H < (C.process (q n) ω K).toReal then
      {z : upperHalfPlane | (z:ℂ)∈γ ω '' Icc 0 (q n)}ᶜ else ∅)
  have hJ : Monotone J := fun n m hnm => Finset.image_subset_image (Finset.range_mono hnm)
  have hD : (∫⁻ ω, D ω ∂P) ≤ A := by
    have hh := C.countable_strict_past_le_of_finite_bound hB hc h0 hκ hκ8 F hw
      u hu hmono hlim J hJ E hE K hK A hbound
    simpa only [D, E, J, mem_ofPred_eq, range_image_event_union] using hh
  calc
    _ ≤ ∫⁻ ω, 2*D ω ∂P := by
      apply lintegral_mono_ae
      filter_upwards [C.past_threshold_detects_half_terminal hB hc h0 hκ hκ8 F hw q hq K hK H hH] with ω hω
      by_cases hb : ENNReal.ofReal (2*H) < C.rational.terminal ω K
      · rw [indicator_of_mem (show ω ∈ {ω | ENNReal.ofReal (2*H) < C.rational.terminal ω K} from hb)]
        exact hω hb
      · rw [indicator_of_notMem (show ω ∉ {ω | ENNReal.ofReal (2*H) < C.rational.terminal ω K} from hb)]
        exact bot_le
    _ = 2*(∫⁻ ω, D ω ∂P) := lintegral_const_mul' _ _ (by norm_num)
    _ ≤ 2*A := mul_le_mul' le_rfl hD

end CanonicalMass
end SLEExactGauge.Multipoint

end

end OAI
