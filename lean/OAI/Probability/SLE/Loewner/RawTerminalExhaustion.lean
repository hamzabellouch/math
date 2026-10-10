import OAI.Probability.SLE.Geometry.CanonicalRawTerminal
import OAI.Probability.SLE.Mass.RawMassPathLaw

namespace OAI

/-! A measurable terminal certificate for the raw finite-time mass.
Together with monotonicity it yields terminal domination and local
exhaustion at all real times, not just integer times. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped Topology NNReal ENNReal CompactlySupported

namespace SLEExactGauge

local instance rawExhaustionDriverMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance rawExhaustionDriverBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩
local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

lemma ennreal_antitone_tendsto_zero_of_nat
    (f : ℝ≥0 → ℝ≥0∞) (hf : Antitone f)
    (hn : Tendsto (fun n : ℕ => f n) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  have hi : (⨅ t, f t)=0 := by
    apply le_antisymm ?_ bot_le
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hn (fun n => iInf_le f (n:ℝ≥0))
  simpa only [hi] using tendsto_atTop_iInf hf

def RawTerminalGood (D : LocalTestFamily upperHalfPlane)
    (N : ℝ≥0 → Measure upperHalfPlane) (ν : Measure upperHalfPlane) : Prop :=
  (∀ n : ℕ, ∀ j, (∫ z, (D.test j ⊔ 0) z ∂N n) ≤ ∫ z, (D.test j ⊔ 0) z ∂ν) ∧
  ∀ k, Tendsto (fun n : ℕ => ν (D.compactSet k)-N n (D.compactSet k)) atTop (𝓝 0)

theorem measurableSet_rawTerminalGood
    {Y : Type*} [MeasurableSpace Y] (D : LocalTestFamily upperHalfPlane)
    (N : ℝ≥0 → Y → Measure upperHalfPlane) (ν : Y → Measure upperHalfPlane)
    (hNm : ∀ n : ℕ, Measurable (N n)) (hνm : Measurable ν)
    (hNr : ∀ n : ℕ, ∀ y, (N n y).Regular) (hνr : ∀ y, (ν y).Regular) :
    MeasurableSet {y | RawTerminalGood D (fun t => N t y) (ν y)} := by
  have ho : MeasurableSet {y | ∀ n : ℕ, ∀ j,
      (∫ z, (D.test j ⊔ 0) z ∂N n y) ≤ ∫ z, (D.test j ⊔ 0) z ∂ν y} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun j =>
      measurableSet_le
        (measurable_halfPlane_compact_test_integral (N n) (hNm n) (hNr n) _)
        (measurable_halfPlane_compact_test_integral ν hνm hνr _)
  have ht : MeasurableSet {y | ∀ k, Tendsto
      (fun n : ℕ => ν y (D.compactSet k)-N n y (D.compactSet k)) atTop (𝓝 0)} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro k
    exact measurableSet_tendsto (𝓝 (0:ℝ≥0∞)) (fun n =>
      ((Measure.measurable_coe (D.isCompact k).measurableSet).comp hνm).sub
        ((Measure.measurable_coe (D.isCompact k).measurableSet).comp (hNm n)))
  simpa only [RawTerminalGood,Set.ofPred_and] using ho.inter ht

theorem RawTerminalGood.domination_exhaustion
    (D : LocalTestFamily upperHalfPlane)
    (N : ℝ≥0 → Measure upperHalfPlane) (ν : Measure upperHalfPlane)
    (hNr : ∀ t, (N t).Regular) (hνr : ν.Regular) (hN : Monotone N)
    (hg : RawTerminalGood D N ν) :
    (∀ t, N t ≤ ν) ∧ ∀ K : Set upperHalfPlane, IsCompact K →
      Tendsto (fun t : ℝ≥0 => (ν-N t) K) atTop (𝓝 0) := by
  let := hνr
  have hn (n : ℕ) : N n ≤ ν := by
    let := hNr n
    exact D.measure_le_of_positive_tests _ _ (hg.1 n)
  have hdom (t : ℝ≥0) : N t ≤ ν := by
    obtain ⟨n,hn'⟩ := exists_nat_ge (t:ℝ)
    have ht : t ≤ (n:ℝ≥0) := by exact_mod_cast hn'
    exact (hN ht).trans (hn n)
  refine ⟨hdom,?_⟩
  intro K hK
  obtain ⟨k,hKk⟩ := D.exhaustive K hK
  have hanti : Antitone (fun t : ℝ≥0 => ν (D.compactSet k)-N t (D.compactSet k)) := by
    intro s t hst
    exact tsub_le_tsub_left (hN hst (D.compactSet k)) _
  have hk := ennreal_antitone_tendsto_zero_of_nat _ hanti (hg.2 k)
  have he (t : ℝ≥0) : (ν-N t) (D.compactSet k) =
      ν (D.compactSet k)-N t (D.compactSet k) := by
    let := hNr t
    exact sub_apply_of_finite_restriction (hdom t) (D.isCompact k).measurableSet
      (D.isCompact k).measure_lt_top.ne
  have hk' : Tendsto (fun t : ℝ≥0 => (ν-N t) (D.compactSet k)) atTop (𝓝 0) := by
    simpa only [he] using hk
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hk'
    (fun _ => bot_le) (fun _ => measure_mono hKk)

theorem rawTerminalGood_of_exhaustion
    (D : LocalTestFamily upperHalfPlane)
    (N : ℝ≥0 → Measure upperHalfPlane) (ν : Measure upperHalfPlane)
    (hNr : ∀ t, (N t).Regular) (hνr : ν.Regular)
    (hdom : ∀ t, N t ≤ ν)
    (hlim : ∀ K : Set upperHalfPlane, IsCompact K →
      Tendsto (fun t : ℝ≥0 => (ν-N t) K) atTop (𝓝 0)) :
    RawTerminalGood D N ν := by
  let := hνr
  constructor
  · intro n j
    exact integral_mono_measure (hdom n) (ae_of_all _ (fun _ => le_max_right _ _))
      (D.test j ⊔ 0).integrable
  · intro k
    have he (n : ℕ) : (ν-N n) (D.compactSet k) =
        ν (D.compactSet k)-N n (D.compactSet k) := by
      let := hNr n
      exact sub_apply_of_finite_restriction (hdom n) (D.isCompact k).measurableSet
        (D.isCompact k).measure_lt_top.ne
    simpa only [Function.comp_def,he] using (hlim _ (D.isCompact k)).comp (tendsto_natCast_atTop_atTop (R := ℝ≥0))

namespace Multipoint

theorem CanonicalMass.raw_terminal_good_set
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G)
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (R : ℝ≥0 → C(ℝ≥0,ℝ) → Measure upperHalfPlane)
    (hRp : IsProgressive driverPathFiltration R)
    (hRr : ∀ t p, (R t p).Regular ∧ IsFiniteMeasureOnCompacts (R t p))
    (he : ∀ᵐ ω ∂P, ∀ t, R t (sourceDriverPath B hBc ω)=C.process t ω) :
    let D := localTestFamily upperHalfPlane
    let E : Set C(ℝ≥0,ℝ) := {p | RawTerminalGood D (fun t => R t p) (rawTerminalMass R p)}
    MeasurableSet E ∧ (∀ᵐ p ∂P.map (sourceDriverPath B hBc), p ∈ E) ∧
    ∀ p ∈ E, Monotone (fun t => R t p) →
      (∀ t, R t p ≤ rawTerminalMass R p) ∧
      ∀ K : Set upperHalfPlane, IsCompact K →
        Tendsto (fun t : ℝ≥0 => (rawTerminalMass R p-R t p) K) atTop (𝓝 0) := by
  dsimp only
  have hE := measurableSet_rawTerminalGood (localTestFamily upperHalfPlane) R (rawTerminalMass R)
    (fun n => hRp.adapted.measurable (i := (n:ℝ≥0)))
    (rawTerminalMass_measurable R hRp hRr) (fun n p => (hRr n p).1)
    (fun p => (rawTerminalMass_radon R p).1)
  refine ⟨hE,?_,?_⟩
  · have hp : Measurable (sourceDriverPath B hBc) := source_path_measurable _
      (fun t => hBm.comp (measurable_const.prodMk measurable_id))
    apply (ae_map_iff hp.aemeasurable hE).mpr
    filter_upwards [he,C.rawTerminal_realizes hBc R he,C.paths,C.exhaustion] with ω hω hterm hpath hex
    simp_rw [hω,hterm]
    exact rawTerminalGood_of_exhaustion (localTestFamily upperHalfPlane)
      (fun t => C.process t ω) (C.rational.terminal ω)
      (fun t => (C.radon t ω).1) (C.rational.terminal_radon ω).1 hpath.dominated hex
  · intro p hp hm
    exact RawTerminalGood.domination_exhaustion (localTestFamily upperHalfPlane)
      (fun t => R t p) (rawTerminalMass R p) (fun t => (hRr t p).1)
      (rawTerminalMass_radon R p).1 hm hp

end Multipoint
end SLEExactGauge

end

end OAI
