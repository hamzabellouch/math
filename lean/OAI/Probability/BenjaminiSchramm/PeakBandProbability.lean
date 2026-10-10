import OAI.Probability.BenjaminiSchramm.NormalizedPeakSurgery
import OAI.Probability.BenjaminiSchramm.BandMomentSummability

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def strictPeakBandEvent (a : V → ℝ) (l u : ℝ) (x : V) : Set (Set E) :=
  {ω | ∃ z, l < G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ u ∧
    ω ∈ strictHeightPeakConnection G.ends (G.orbitAdjustedHeight a x) x z}

lemma strictPeakBandEvent_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (l u : ℝ)
    (φ : G.Aut) (ω : Set E) (x : V) :
    φ.edge '' ω ∈ G.strictPeakBandEvent a l u (φ.vertex x) ↔
      ω ∈ G.strictPeakBandEvent a l u x := by
  have hconn (v w : V) : Percolation.Conn G.ends (φ.edge '' ω) (φ.vertex v) (φ.vertex w) ↔
      Percolation.Conn G.ends ω v w := by
    rw [←Percolation.conn_aut_iff G.ends φ.preserves,
      Set.preimage_image_eq _ φ.edge.injective]
  have hpeak (z : V) : φ.edge '' ω ∈ strictHeightPeakConnection G.ends
      (G.orbitAdjustedHeight a (φ.vertex x)) (φ.vertex x) (φ.vertex z) ↔
      ω ∈ strictHeightPeakConnection G.ends (G.orbitAdjustedHeight a x) x z := by
    constructor
    · rintro ⟨h,hp⟩
      refine ⟨(hconn x z).mp h,fun y hy hyz => ?_⟩
      have hh := hp (φ.vertex y) ((hconn z y).mpr hy) (fun he => hyz (φ.vertex.injective he))
      simpa only [G.orbitAdjustedHeight_aut a ha] using hh
    · rintro ⟨h,hp⟩
      refine ⟨(hconn x z).mpr h,?_⟩
      intro y hy hyz
      obtain ⟨v,rfl⟩ := φ.vertex.surjective y
      have hh := hp v ((hconn z v).mp hy) (fun he => hyz (congrArg φ.vertex he))
      simpa only [G.orbitAdjustedHeight_aut a ha] using hh
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨v,rfl⟩ := φ.vertex.surjective z
    refine ⟨v,?_⟩
    simpa only [G.orbitAdjustedHeight_aut a ha,hpeak] using hz
  · rintro ⟨z,hz⟩
    refine ⟨φ.vertex z,?_⟩
    simpa only [G.orbitAdjustedHeight_aut a ha,hpeak] using hz

variable [Countable V] [Countable E]

lemma measurableSet_strictPeakBandEvent (a : V → ℝ) (l u : ℝ) (x : V) :
    MeasurableSet (G.strictPeakBandEvent a l u x) := by
  exact (Measurable.exists fun z => measurable_const.and
    (measurable_const.and (measurableSet_strictHeightPeakConnection G.ends _ x z).mem)).setOf

lemma strictPeakBandEvent_probability_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (l u : ℝ)
    (φ : G.Aut) (p : unitInterval) (x : V) :
    G.law p (G.strictPeakBandEvent a l u (φ.vertex x)) =
      G.law p (G.strictPeakBandEvent a l u x) := by
  conv_lhs => rw [←G.law_map_aut p φ]
  rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
    (G.measurableSet_strictPeakBandEvent a l u _)]
  congr 1
  ext ω
  exact G.strictPeakBandEvent_aut a ha l u φ ω x

lemma strictPeakBandEvent_probability_le_weighted_roots
    (O : G.OrbitRepresentatives) (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (m : ℝ) (ham : ∀ x, m ≤ a x) (p : unitInterval) (l u : ℝ) (x : V) :
    ENNReal.ofReal m*G.law p (G.strictPeakBandEvent a l u x) ≤
      ∑ r ∈ O.roots, ENNReal.ofReal (a r)*G.law p (G.strictPeakBandEvent a l u r) := by
  obtain ⟨r,hr,φ,rfl⟩ := O.cover x
  rw [G.strictPeakBandEvent_probability_aut a ha l u φ p r]
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (ham r)) le_rfl).trans
    (Finset.single_le_sum (f := fun r => ENNReal.ofReal (a r)*G.law p (G.strictPeakBandEvent a l u r))
      (fun _ _ => bot_le) hr)

end CriticalPercolation.BondGraph

end

end OAI
